{-# LANGUAGE BangPatterns #-}

module Cardano.Wallet.Kernel.CoinSelection.Generic.Fees (
    ExpenseRegulation(..)
  , FeeOptions(..)
  , adjustForFees
  ) where

import           Universum

import           Control.Monad.Trans.Except (Except)
import           Formatting (bprint)
import           Formatting.Buildable (Buildable (..))

import           Cardano.Wallet.Kernel.CoinSelection.Generic

{-------------------------------------------------------------------------------
  Top-level API
-------------------------------------------------------------------------------}

data ExpenseRegulation =
      SenderPaysFee
    -- ^ The sender pays for the fee. This is the typical case.
    | ReceiverPaysFee
    -- ^ The receiver pays for the fee. This is useful for cases
    -- where users wants to transfer funds between wallets owned by them,
    -- and they wish to trasfer an @exact@ amount (or, for example, the max
    -- amount).

data FeeOptions dom = FeeOptions {
      -- | Estimate fees based on number of inputs and values of the outputs
      foEstimate          :: Int -> [Value dom] -> Fee dom

      -- | Expense regulation (who pays the fees?)
    , foExpenseRegulation :: ExpenseRegulation
    }

-- | Given the coin selection result from a policy run, adjust the outputs
-- for fees, potentially returning additional inputs that we need to cover
-- all fees.
adjustForFees :: forall utxo m. (CoinSelDom (Dom utxo), Monad m)
              => FeeOptions (Dom utxo)
              -> (Value (Dom utxo) ->
                   CoinSelT utxo CoinSelHardErr m (Maybe (UtxoEntry (Dom utxo))))
              -> [CoinSelResult (Dom utxo)]
              -> CoinSelT utxo CoinSelHardErr m
                   ([CoinSelResult (Dom utxo)], SelectedUtxo (Dom utxo), Value (Dom utxo))
adjustForFees feeOptions pickUtxo css = do
    case foExpenseRegulation feeOptions of
      ReceiverPaysFee -> coinSelLiftExcept $
        (, emptySelection, valueZero) <$> receiverPaysFee upperBound css
      SenderPaysFee ->
        senderPaysFee feeOptions pickUtxo upperBound css
  where
    upperBound = feeUpperBound feeOptions css

{-------------------------------------------------------------------------------
  Receiver pays fee
-------------------------------------------------------------------------------}

receiverPaysFee :: forall dom. CoinSelDom dom
                => Fee dom
                -> [CoinSelResult dom]
                -> Except CoinSelHardErr [CoinSelResult dom]
receiverPaysFee totalFee =
    mapM go . divvyFee (outVal . coinSelRequest) totalFee
  where
    go :: (Fee dom, CoinSelResult dom)
       -> Except CoinSelHardErr (CoinSelResult dom)
    go (fee, cs) =
        case outSubFee fee (coinSelRequest cs) of
          Just newOut ->
            return $ cs { coinSelOutput = newOut }
          Nothing ->
            throwError $
              CoinSelHardErrOutputCannotCoverFee (pretty (coinSelRequest cs)) (pretty fee)

{-------------------------------------------------------------------------------
  Sender pays fee
-------------------------------------------------------------------------------}

senderPaysFee :: (Monad m, CoinSelDom (Dom utxo))
              => FeeOptions (Dom utxo)
              -> (Value (Dom utxo) ->
                   CoinSelT utxo CoinSelHardErr m (Maybe (UtxoEntry (Dom utxo))))
              -> Fee (Dom utxo)
              -> [CoinSelResult (Dom utxo)]
              -> CoinSelT utxo CoinSelHardErr m
                   ([CoinSelResult (Dom utxo)], SelectedUtxo (Dom utxo), Value (Dom utxo))
senderPaysFee feeOptions pickUtxo totalFee css = do
    let (css', remainingFee) = feeFromChange totalFee css
    -- unsafe because it's the remaining. These are the fees css' has payed.
    let feePayed = unsafeFeeSub totalFee remainingFee
    let adjustedEstimatedFees = feeUpperBoundAdjusted feeOptions -- c u
    let adjustedPayedFees u = unsafeValueAdd (getFee feePayed) (selectedBalance u)
    -- we pick some inputs, until we cover all fees and we have a positive change.
    -- After picking each input, we readjust the fees by applying the partial function.
    (additionalUtxo, additionalChange) <-
        coverRemainingFee pickUtxo (adjustedEstimatedFees css') adjustedPayedFees
    -- at this point we have a positive change, but we are not done yet. If we
    -- return the whole change, we may create new fees which we can't cover.
    -- On the other hand if we return none, this is for sure an accepted tx,
    -- but we may have payed huge fees. The truth lies in the middle: we can do
    -- binary search.
    let css'' = binarySearch (\c -> getFee $ adjustedEstimatedFees c additionalUtxo) css' additionalChange
    return (css', additionalUtxo, additionalChange)


coverRemainingFee :: forall utxo m. (Monad m, CoinSelDom (Dom utxo))
                  => (Value (Dom utxo) -> CoinSelT utxo CoinSelHardErr m (Maybe (UtxoEntry (Dom utxo))))
                  -> (SelectedUtxo (Dom utxo) -> Fee (Dom utxo))
                  -> (SelectedUtxo (Dom utxo) -> Value (Dom utxo))
                  -> CoinSelT utxo CoinSelHardErr m (SelectedUtxo (Dom utxo), Value (Dom utxo))
coverRemainingFee pickUtxo adjustedEstimatedFees adjustedPayedFees =
    go emptySelection
  where
    -- we pick utxos until we have positive change.
    go :: SelectedUtxo (Dom utxo)
       -> CoinSelT utxo CoinSelHardErr m (SelectedUtxo (Dom utxo), Value (Dom utxo))
    go !acc =
      let
          payed = adjustedPayedFees acc
          estimated = getFee (adjustedEstimatedFees acc)
      in if payed >= estimated
         then return (acc, unsafeValueSub payed estimated)
         else do
            mio <- (pickUtxo $ unsafeValueSub estimated payed)
            io  <- maybe (throwError CoinSelHardErrCannotCoverFee) return mio
            let newSelected = select io acc
            go newSelected

-- we have:
-- adjustedFees css <= change
-- we search for the biggest c such that:
-- adjustedFees (splitChange c css) >= change - c
binarySearch :: forall dom. CoinSelDom dom =>
             -> ([CoinSelResult dom] -> Value (Dom utxo))
             -> [CoinSelResult dom]
             -> Value (Dom utxo)
             -> [CoinSelResult dom]
binarySearch adjustedFees css initialValue = go
  where
    initialFee = adjustedFees css
    check v =
      let
        css' = split v css
        fee' = adjustedFees css'
        newFee = unsafeValueSub fee' initialFee
      in initialValue >= newFee

    half = splitChange (div v 2) css


splitChange :: forall dom. CoinSelDom dom
            => Value dom -> [CoinSelResult dom] -> [CoinSelResult dom]
splitChange = go
  where
    go remaining [] = error "empty coinResult"
    go remaining [cs] =
      let changes = coinSelChange cs
      in [cs {coinSelChange = addToList remaining changes}]
    go remaining css@(cs : csRest) =
      let piece = valueDiv remaining (length css) -- length cannot be 0.
          newRemaining = unsafeValueSub remaining piece -- unsafe because of div.
      in case addToListMaybe piece (coinSelChange cs) of
          Just newChanges -> cs {coinSelChange = newChanges} : go newRemaining csRest
          Nothing        -> cs : go remaining csRest

addToList :: (IsValue (Value dom)) => Value dom -> [Value dom] -> [Value dom]
addToList v [] = [v]
addToList v (x:xs) = case valueAdd v x of
    Just newValue -> newValue : xs
    Nothing        -> addToList v xs

-- | same as @addToList@, but it tries to avoid to create a new change output.
-- if it can't, it returns Nothing.
addToListMaybe :: (IsValue (Value dom)) => Value dom -> [Value dom] -> Maybe [Value dom]
addToListMaybe v [] = Nothing
addToListMaybe v (x:xs) = case valueAdd v x of
    Just newValue -> Just $ newValue : xs
    Nothing        -> addToListMaybe v xs

-- | Attempt to pay the fee from change outputs, returning any fee remaining
--
-- NOTE: For sender pays fees, distributing the fee proportionally over the
-- outputs is not strictly necessary (fairness is not a concern): we could just
-- use the change of the first output to cover the entire fee (if sufficiently
-- large). Doing it proportionally however has the benefit that the fee
-- adjustment doesn't change the payment:change ratio too much, which may be
-- important for the correct operation of the coin selection policy.
--
-- NOTE: This does mean that /if/ the policy generates small outputs with
-- very large corresponding change outputs, we may not make optional use of
-- those change outputs and perhaps unnecessarily add additional UTxO entries.
-- However, in most cases the policy cares about the output:change ratio,
-- so we stick with this approach nonetheless.
feeFromChange :: forall dom. CoinSelDom dom
              => Fee dom
              -> [CoinSelResult dom]
              -> ([CoinSelResult dom], Fee dom)
feeFromChange totalFee =
    bimap identity unsafeFeeSum
    . unzip
    . map go
    . divvyFee (outVal . coinSelRequest) totalFee
  where
    -- | Adjust the change output, returning any fee remaining
    go :: (Fee dom, CoinSelResult dom) -> (CoinSelResult dom, Fee dom)
    go (fee, cs) =
        let (change', fee') = reduceChangeOutputs fee (coinSelChange cs)
        in (cs { coinSelChange = change' }, fee')

-- | Reduce the given change outputs by the total fee, returning the remainig
-- change outputs if any are left, or the remaining fee otherwise
--
-- As for the overall fee in 'feeFromChange', we divvy up the fee over all
-- change outputs proportionally, to try and keep any output:change ratio
-- as unchanged as possible
reduceChangeOutputs :: forall dom. CoinSelDom dom
                    => Fee dom -> [Value dom] -> ([Value dom], Fee dom)
reduceChangeOutputs totalFee cs =
    case divvyFeeSafe identity totalFee cs of
        Nothing ->
            (cs, totalFee)
        Just xs ->
            bimap identity unsafeFeeSum
            . unzip
            . map go
            $ xs
  where
    -- Reduce single change output, returning remaining fee
    go :: (Fee dom, Value dom) -> (Value dom, Fee dom)
    go (fee, change)
      | change >= getFee fee =
          (unsafeValueSub change (getFee fee), Fee valueZero)
      | otherwise =
          (valueZero, adjustFee (`unsafeValueSub` change) fee)

{-------------------------------------------------------------------------------
  Auxiliary
-------------------------------------------------------------------------------}

feeUpperBound :: CoinSelDom dom
              => FeeOptions dom -> [CoinSelResult dom] -> Fee dom
feeUpperBound FeeOptions{..} css =
    foEstimate numInputs outputs
  where
    numInputs = fromIntegral $ sum (map (sizeToWord . coinSelInputSize) css)
    outputs   = concatMap coinSelOutputs css

feeUpperBoundAdjusted :: CoinSelDom dom
                      => FeeOptions dom -> [CoinSelResult dom]
                      -> SelectedUtxo (dom)
                      -> Fee dom
feeUpperBoundAdjusted FeeOptions{..} css utxos =
  foEstimate numInputs outputs
  where
    numInputs = fromIntegral $ sum $ sizeToWord <$>
                  (selectedSize utxos : map coinSelInputSize css)
    outputs   = concatMap coinSelOutputs css

-- | divvy fee across outputs, discarding zero-output if any. Returns `Nothing`
-- when there's no more outputs after filtering, in which case, we just can't
-- divvy fee.
divvyFeeSafe
    :: forall dom a. CoinSelDom dom
    => (a -> Value dom)
    -> Fee dom
    -> [a]
    -> Maybe [(Fee dom, a)]
divvyFeeSafe f fee as = case filter ((/= valueZero) . f) as of
    []  -> Nothing
    as' -> Just (divvyFee f fee as')

{-------------------------------------------------------------------------------
  Pretty-printing
-------------------------------------------------------------------------------}

instance Buildable ExpenseRegulation where
    build SenderPaysFee   = bprint "SenderPaysFee"
    build ReceiverPaysFee = bprint "ReceiverPaysFee"
