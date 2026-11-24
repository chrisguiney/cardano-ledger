{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}

module Cardano.Chain.Update.ProtocolVersion (
  ProtocolVersion (..),
) where

import Cardano.Ledger.Binary (
  DecCBOR (..),
  EncCBOR (..),
  FromCBOR (..),
  ToCBOR (..),
  Version,
  encodeListLen,
  enforceSize,
  fromByronCBOR,
  getVersion64,
  mkVersion,
  toByronCBOR,
 )
import Cardano.Prelude
import Data.Aeson (ToJSON)
import Formatting (bprint, shown)
import Formatting.Buildable (Buildable (..))
import NoThunks.Class (NoThunks (..))
import qualified Prelude

-- | Communication protocol version
data ProtocolVersion = ProtocolVersion
  { pvMajor :: !Version
  -- ^ Bounded by 'Cardano.Ledger.Binary.MaxVersion', as the later eras' major
  -- versions are. It is still encoded as a 'Word16'.
  , pvMinor :: !Word16
  , pvAlt :: !Word8
  }
  deriving (Eq, Generic, Ord)
  deriving anyclass (NFData, NoThunks)

instance Show ProtocolVersion where
  show pv =
    intercalate "." [show (getVersion64 (pvMajor pv)), show (pvMinor pv), show (pvAlt pv)]

instance Buildable ProtocolVersion where
  build = bprint shown

-- Used for debugging purposes only
instance ToJSON ProtocolVersion

instance ToCBOR ProtocolVersion where
  toCBOR = toByronCBOR
  encodedSizeExpr f pv =
    1
      + encodedSizeExpr f (majorWord16 . pvMajor <$> pv)
      + encodedSizeExpr f (pvMinor <$> pv)
      + encodedSizeExpr f (pvAlt <$> pv)

instance FromCBOR ProtocolVersion where
  fromCBOR = fromByronCBOR

instance EncCBOR ProtocolVersion where
  encCBOR pv =
    encodeListLen 3
      <> encCBOR (majorWord16 (pvMajor pv))
      <> encCBOR (pvMinor pv)
      <> encCBOR (pvAlt pv)

instance DecCBOR ProtocolVersion where
  decCBOR = do
    enforceSize "ProtocolVersion" 3
    ProtocolVersion <$> (mkVersion =<< decCBOR @Word16) <*> decCBOR <*> decCBOR

-- | The major version as the codec has always written it: a 'Word16', which
-- holds every 'Version', since 'Cardano.Ledger.Binary.MaxVersion' is far below
-- its bound.
majorWord16 :: Version -> Word16
majorWord16 = fromIntegral . getVersion64
