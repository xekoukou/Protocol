module Serialize where

open import Agda.Primitive
open import Prelude.Nat
open import Prelude.Unit
open import Prelude.String
open import Prelude.Int
open import Prelude.Bool
open import Builtin.Float



{-# FOREIGN GHC 

import qualified Data.ByteString.Lazy as BL
import Data.Binary

unitToBS :: () -> BL.ByteString
unitToBS x = encode x

bsToUnit :: BL.ByteString -> ()
bsToUnit x = decode x

boolToBS :: Bool -> BL.ByteString
boolToBS x = encode x

bsToBool :: BL.ByteString -> Bool
bsToBool x = decode x

intToBS :: Integer -> BL.ByteString
intToBS x = encode x

bsToInt :: BL.ByteString -> Integer
bsToInt x = decode x

floatToBS :: Double -> BL.ByteString
floatToBS x = encode x

bsToFloat :: BL.ByteString -> Double
bsToFloat x = decode x

stringToBS :: Data.Text.Text -> BL.ByteString
stringToBS x = encode x

bsToString :: BL.ByteString -> Data.Text.Text
bsToString x = decode x


#-}

postulate
  LByteString : Set
  natToBS : Nat → LByteString
  bsToNat : LByteString → Nat
  unitToBS : ⊤ → LByteString
  boolToBS : Bool → LByteString
  bsToBool : LByteString → Bool
  bsToUnit : LByteString → ⊤
  intToBS : Int → LByteString
  bsToInt : LByteString → Int
  floatToBS : Float → LByteString
  bsToFloat : LByteString → Float
  stringToBS : String → LByteString
  bsToString : LByteString → String


{-# COMPILE GHC LByteString = type BL.ByteString #-}
{-# COMPILE GHC natToBS = intToBS #-}
{-# COMPILE GHC bsToNat = bsToInt #-}
{-# COMPILE GHC unitToBS = unitToBS #-}
{-# COMPILE GHC bsToUnit = bsToUnit #-}
{-# COMPILE GHC boolToBS = boolToBS #-}
{-# COMPILE GHC bsToBool = bsToBool #-}
{-# COMPILE GHC intToBS = intToBS #-}
{-# COMPILE GHC bsToInt = bsToInt #-}
{-# COMPILE GHC floatToBS = floatToBS #-}
{-# COMPILE GHC bsToFloat = bsToFloat #-}
{-# COMPILE GHC stringToBS = stringToBS #-}
{-# COMPILE GHC bsToString = bsToString #-}




record Serializable {ℓ} (A : Set ℓ) : Set ℓ where
  field
    encode : A → LByteString
    decode : LByteString → A



open Serializable {{...}} public

instance

  SerializableString : Serializable String
  encode {{SerializableString}} = stringToBS
  decode {{SerializableString}} = bsToString

  SerializableUnit : Serializable ⊤ 
  encode {{SerializableUnit}} = unitToBS
  decode {{SerializableUnit}} = bsToUnit


  SerializableNat : Serializable Nat
  encode {{SerializableNat}} = natToBS
  decode {{SerializableNat}} = bsToNat
