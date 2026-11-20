{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE UndecidableSuperClasses #-}

-- | Re-construction of an announced `EndorserBlock`, for Leios committee members that
-- need to decide whether to vote for it.
--
-- The committee member knows the `EbReferences` from the announcement, but not the
-- transactions themselves: those diffuse separately and are fetched one by one. This
-- interface accepts them as they are resolved and reproduces, step by step, the verdict
-- that the @EB@ rule will later reach on the same endorser block.
module Cardano.Ledger.Dijkstra.Block.Endorser.ReBuilder (
  EbReBuilderState,
  EbReBuilderInitError (..),
  EbReBuilderError (..),
  EbReBuilderResult (..),
  EbReBuilderFinalizerError (..),
  EraEndorserBlockReBuilder (..),
  modifyEbReBuilderStateUTxO,
) where

import Cardano.Ledger.BaseTypes
import Cardano.Ledger.Core
import Cardano.Ledger.Dijkstra ()
import Cardano.Ledger.Dijkstra.Block.Endorser (EraEndorserBlock (..))
import Cardano.Ledger.Dijkstra.Era (DijkstraEra)
import Cardano.Ledger.Dijkstra.PParams (DijkstraEraPParams, ppMaxEndorserBlockTxsSizeL)
import Cardano.Ledger.Dijkstra.Rules.Eb (
  EbAlreadyApplied (..),
  EbAnnouncementHashMismatch (..),
  EbAnnouncementSizeMismatch (..),
  EbAnnouncementSlotMismatch (..),
  EbPredFailure (..),
  EbReferencesSizeTooBig (..),
  EbWasNotAnnounced (..),
  validateEbAnnouncementSlot,
  validateEbReferences,
 )
import Cardano.Ledger.Dijkstra.Rules.Ledger (DijkstraLedgerPredFailure)
import Cardano.Ledger.Shelley.API (ApplyTx (..), MempoolTx, ValidatedTx)
import Cardano.Ledger.Shelley.LedgerState
import Cardano.Ledger.State (CanSetUTxO (..), EraGov, UTxO)
import Control.State.Transition (PredicateFailure)
import Data.Bifunctor (first)
import Data.List.NonEmpty (NonEmpty)
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Sequence.Strict (StrictSeq)
import Data.SimpleOMap.Strict (assocList)
import qualified Data.Vector.Primitive as P
import qualified Data.Vector.Storable as S
import Data.Word (Word32)
import GHC.Generics (Generic)
import Lens.Micro ((%~), (&), (^.))
import Validation (validationToEither)

{-
Q
1) order in Vectors is the same as the order in EbReferences
2) EbReBuilderInitError - reuse of predicate failures defined in Eb
3)

-}

-- | Running state for the re-construction of an announced `EndorserBlock`.
data EbReBuilderState era = EbReBuilderState
  { ebrbsEbReferences :: !(EbReferences era)
  -- ^ The announced references, as supplied at initialisation.
  , ebrbsTxHashes :: !(S.Vector (SafeHash EraIndependentTx))
  -- ^ The referenced transaction hashes, in the same order as in `EbReferences`
  , ebrbsTxSizes :: !(P.Vector Word32)
  -- ^ The declared transaction sizes, in the same order as `ebrbsTxHashes`.
  , ebrbsStAnnTxs :: !(Map (SafeHash EraIndependentTx) (StAnnTx TopTx era))
  -- ^ The transactions resolved so far.
  , ebrbsBlockBodyLimits :: !(BlockBodyLimits era)
  -- ^ Totals accumulated across the transactions applied so far.
  , ebrbsNewEpochState :: !(NewEpochState era)
  -- ^ The state the transactions applied so far have produced.
  }
  deriving (Generic)

data EbReBuilderInitError era
  = EbReBuilderInitNoAnnouncement !(EbWasNotAnnounced era)
  | EbReBuilderInitEbReferencesSizeTooBig !(EbReferencesSizeTooBig era)
  | EbReBuilderInitEbAnnouncementHashMismatch !(EbAnnouncementHashMismatch era)
  | EbReBuilderInitEbAnnouncementSizeMismatch !(EbAnnouncementSizeMismatch era)
  | EbReBuilderInitEbAnnouncementSlotMismatch !(EbAnnouncementSlotMismatch era)
  | EbReBuilderInitEbAlreadyApplied !(EbAlreadyApplied era)
  | -- | The declared transaction sizes add up to more than `ppMaxEndorserBlockTxsSizeL`
    EbReBuilderInitTxsSizeTooBig !(Mismatch RelLTEQ Int)
  deriving (Eq, Show, Generic)

-- | An inconsistency between the endorser block being re-constructed and the references
-- that were announced for it.
data EbReBuilderError era
  = -- | The supplied transaction is not the one the references name at this position.
    EbReBuilderTxHashMismatch !TxIx !(Mismatch RelEQ (SafeHash EraIndependentTx))
  | -- | The supplied transaction is not the size the references declare for it.
    EbReBuilderTxSizeMismatch !TxIx !(Mismatch RelEQ Word32)
  deriving (Eq, Show, Generic)

data EbReBuilderResult era
  = EbReBuilderSuccess !(EbReBuilderState era) !(ValidatedTx era)
  | -- | The endorser block is inconsistent with its announced references.
    EbReBuilderError !(EbReBuilderError era) !(ValidatedTx era)
  | -- | The transaction itself did not validate.
    EbReBuilderTxError !TxIx !(EbReBuilderTxError era)
  deriving (Generic)

-- | Produced when finalisation is initiated, but transactions are still expected.
newtype EbReBuilderFinalizerError
  = EbReBuilderMissingTxsError [SafeHash EraIndependentTx]
  deriving (Eq, Show, Generic)

class EraEndorserBlockBuilder era => EraEndorserBlockReBuilder era where
  data EbReBuilderTxError era

  -- | Derive the initial state from the ledger state and the announced references, and
  -- construct an empty `EndorserBlock`.
  mkInitEbReBuilderState ::
    NewEpochState era ->
    EbReferences era ->
    Either (EbReBuilderInitError era) (EbReBuilderState era)

  -- | Resolve the next transaction, checking it against its reference and applying it via
  -- the @LEDGER@ rule.
  snocTxEbReBuilder ::
    Globals ->
    EbReBuilderState era ->
    Either (ValidatedTx era) (MempoolTx era) ->
    EbReBuilderResult era

  -- | Assemble the `EndorserBlock` and return the state its transactions produced
  -- Fails only if some of the referenced transactions were never supplied.
  finalizeEbReBuilder ::
    EbReBuilderState era ->
    Either EbReBuilderFinalizerError (EndorserBlock era, NewEpochState era)

-- | Adjust the `UTxO` that the re-builder validates against.
modifyEbReBuilderStateUTxO ::
  (UTxO era -> UTxO era) -> EbReBuilderState era -> EbReBuilderState era
modifyEbReBuilderStateUTxO f ebReBuilderState@EbReBuilderState {ebrbsNewEpochState} =
  ebReBuilderState {ebrbsNewEpochState = ebrbsNewEpochState & utxoL %~ f}

instance EraEndorserBlockReBuilder DijkstraEra where
  newtype EbReBuilderTxError DijkstraEra
    = DijkstraEbReBuilderTxError (NonEmpty (DijkstraLedgerPredFailure DijkstraEra))

  mkInitEbReBuilderState = mkInitEbReBuilderStateDijkstra

  snocTxEbReBuilder = error "snocTxEbReBuilder: not implemented yet"

  finalizeEbReBuilder = error "finalizeEbReBuilder: not implemented yet"

mkInitEbReBuilderStateDijkstra ::
  forall era.
  ( DijkstraEraPParams era
  , EraBlockBody era
  , EraEndorserBlock era
  , EraGov era
  ) =>
  NewEpochState era ->
  EbReferences era ->
  Either (EbReBuilderInitError era) (EbReBuilderState era)
mkInitEbReBuilderStateDijkstra nes ebRefs = do
  case nes ^. nesEsL . esLStateL . lsLastEbAnnouncementL of
    SNothing ->
      Left $
        EbReBuilderInitNoAnnouncement $
          EbWasNotAnnounced $
            hashAnnotated ebRefs
    SJust ebA -> undefined

-- case nes ^. nesEsL . esLStateL . lsLastEbAnnouncementL of
--   SNothing ->
--     Left . EbReBuilderInitEbFailure . pure . EbWasNotAnnouncedInEB . EbWasNotAnnounced $
--       hashAnnotated ebRefs
--   SJust ebA ->
--     first EbReBuilderInitEbFailure . validationToEither $
--       validateEbReferences pp ebA ebRefs
--         *> first
--           (fmap EbAnnouncementSlotMismatchInEB)
--           (validateEbAnnouncementSlot ebA lastTickSlotNo)
-- validateDeclaredTxsSize
-- pure
--   EbReBuilderState
--     { ebrbsEbReferences = ebRefs
--     , ebrbsTxHashes = S.fromList $ map fst references
--     , ebrbsTxSizes = txSizes
--     , ebrbsStAnnTxs = Map.empty
--     , ebrbsBlockBodyLimits = mempty
--     , ebrbsNewEpochState = nes
--     }
-- where
--   pp = nes ^. nesEsL . curPParamsEpochStateL
--   lastTickSlotNo = nes ^. nesLastTickSlotNoL
--   references = assocList $ ebRefs ^. txRefsEbReferencesG
--   txSizes = P.fromList $ map snd references
--   -- The references declare every transaction's size, so the endorser block's total
--   -- transaction size is known before a single transaction has been resolved. The total
--   -- is accumulated as an `Int`, since a sum of `Word32` sizes need not fit in a `Word32`.
--   validateDeclaredTxsSize
--     | totalTxsSize <= maxTxsSize = Right ()
--     | otherwise =
--         Left $
--           EbReBuilderInitTxsSizeTooBig
--             Mismatch {mismatchSupplied = totalTxsSize, mismatchExpected = maxTxsSize}
--     where
--       totalTxsSize = P.foldl' (\acc -> (acc +) . fromIntegral @Word32 @Int) 0 txSizes
--       maxTxsSize = fromIntegral @Word32 @Int $ pp ^. ppMaxEndorserBlockTxsSizeL

--------------------------------------------------------------------------------------
-- Placeholders, remove with https://github.com/IntersectMBO/cardano-ledger/pull/6284
-------------------------------------------------------------------------------------

data EbBuilderState era = EbBuilderState
  { ebbsStAnnTxs :: !(StrictSeq (StAnnTx TopTx era))
  , ebbsReferencesEntriesSize :: !Int
  , ebbsBlockBodyLimits :: !(BlockBodyLimits era)
  , ebbsNewEpochState :: !(NewEpochState era)
  }
  deriving (Generic)

data EbBuilderResult era
  = EbBuilderSuccess !(EbBuilderState era)
  | EbBuilderLimitExceeded !(NonEmpty (PredicateFailure (EraRule "EB" era)))
  | EbBuilderTxError !(ApplyTxError era)
  deriving (Generic)

class (ApplyTx era, EraEndorserBlock era) => EraEndorserBlockBuilder era where
  mkInitEbBuilderState :: NewEpochState era -> EbBuilderState era
  snocTxEbBuilderValidated :: Globals -> EbBuilderState era -> ValidatedTx era -> EbBuilderResult era
  finalizeEbBuilder :: EbBuilderState era -> Maybe (EndorserBlock era)

instance EraEndorserBlockBuilder DijkstraEra where
  mkInitEbBuilderState = error "placeholder"
  snocTxEbBuilderValidated = error "placeholder"
  finalizeEbBuilder = error "placeholder"
