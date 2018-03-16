module Serialize where

open import Agda.Primitive
open import Prelude.Nat
open import Prelude.Unit
open import Prelude.String
open import Prelude.Int
open import Prelude.Bool
open import Prelude.Product
open import Prelude.Vec
open import Prelude.Word
open import Prelude.Maybe
open import Prelude.Function
open import Prelude.Monad
open import Prelude.Number
open import Prelude.Ord
open import Prelude.Decidable
open import Prelude.Equality
open import Builtin.Float
open import Level hiding (suc ; zero)


{-# FOREIGN GHC 

import qualified Data.ByteString.Lazy as BL
import Data.Binary
import Data.Int


mdecode :: Binary a => BL.ByteString -> Maybe a
mdecode x = case (decodeOrFail x) of
               (Left _) -> Nothing
               (Right (_ , _ , a)) -> Just a

unitToBS :: () -> BL.ByteString
unitToBS x = encode x

bsToUnit :: BL.ByteString -> Maybe ()
bsToUnit x = mdecode x

boolToBS :: Bool -> BL.ByteString
boolToBS x = encode x

bsToBool :: BL.ByteString -> Maybe Bool
bsToBool x = mdecode x

intToBS :: Integer -> BL.ByteString
intToBS x = encode x

bsToInt :: BL.ByteString -> Maybe Integer
bsToInt x = mdecode x

floatToBS :: Double -> BL.ByteString
floatToBS x = encode x

bsToFloat :: BL.ByteString -> Maybe Double
bsToFloat x = mdecode x

stringToBS :: Data.Text.Text -> BL.ByteString
stringToBS x = encode x

bsToString :: BL.ByteString -> Maybe Data.Text.Text
bsToString x = mdecode x

word64ToBS :: Word64 -> BL.ByteString
word64ToBS x = encode x

bsToWord64 :: BL.ByteString -> Maybe Word64
bsToWord64 x = mdecode x

int64ToBS :: Int64 -> BL.ByteString
int64ToBS x = encode x

bsToInt64 :: BL.ByteString -> Maybe Int64
bsToInt64 x = mdecode x

#-}


postulate
  LByteString : Set
  empty : LByteString
  _~~_ : LByteString → LByteString → LByteString
  natToBS : Nat → LByteString
  bsToNat : LByteString → Maybe Nat
  unitToBS : ⊤ → LByteString
  bsToUnit : LByteString → Maybe ⊤
  boolToBS : Bool → LByteString
  bsToBool : LByteString → Maybe Bool
  intToBS : Int → LByteString
  bsToInt : LByteString → Maybe Int
  floatToBS : Float → LByteString
  bsToFloat : LByteString → Maybe Float
  stringToBS : String → LByteString
  bsToString : LByteString → Maybe String
  word64ToBS : Word64 → LByteString
  bsToWord64 : LByteString → Maybe Word64



private

  postulate
    Int64 : Set
    take : Int64 -> LByteString -> LByteString
    drop : Int64 -> LByteString -> LByteString
    length : LByteString → Int64
    int64ToBS : Int64 → LByteString
    bsToInt64 : LByteString → Maybe Int64
    natToInt64 : Nat → Int64
    int64ToNat : Int64 → Nat

{-# COMPILE GHC LByteString = type BL.ByteString #-}
{-# COMPILE GHC Int64 = type Int64 #-}
{-# COMPILE GHC empty = BL.empty #-}
{-# COMPILE GHC take = BL.take #-}
{-# COMPILE GHC drop = BL.drop #-}
{-# COMPILE GHC _~~_ = BL.append #-}
{-# COMPILE GHC length = BL.length #-}
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
{-# COMPILE GHC word64ToBS = word64ToBS #-}
{-# COMPILE GHC bsToWord64 = bsToWord64 #-}
{-# COMPILE GHC natToInt64 = fromIntegral #-}
{-# COMPILE GHC int64ToNat = fromIntegral #-}


splitAt : Nat → LByteString → Maybe (LByteString × LByteString)
splitAt n xs = case (int64ToNat (length xs)) of λ {x → case (isLess (compare n x)) of
                                                       λ { false → let nn = natToInt64 n in just ((take nn xs) , (drop nn xs)) ;
                                                           true → nothing}}

-- Not necessary anymore
instance
  NumberInt64 : Number Int64
  Number.Constraint NumberInt64 _ = ⊤
  fromNat {{NumberInt64}} n = natToInt64 n



record Serializable {a} (A : Set a) : Set a  where
  field
    encode : A → LByteString
    decode : LByteString → Maybe A



open Serializable {{...}} public



instance
 
  SerializableString : Serializable String
  encode ⦃ SerializableString ⦄ x = stringToBS x
  decode {{SerializableString}} x = bsToString x

  SerializableUnit : Serializable ⊤ 
  encode {{SerializableUnit}} x = unitToBS x
  decode {{SerializableUnit}} x = bsToUnit x


  SerializableNat : Serializable Nat
  encode {{SerializableNat}} x = natToBS x
  decode {{SerializableNat}} x = bsToNat x


  SerializableUNat : Serializable (Σ ⊤ (λ _ → Nat))
  encode ⦃ SerializableUNat ⦄ (_ , x) = encode x
  decode {{SerializableUNat}} x = decode x >>= λ x → just (unit , x)



  {-# NON_TERMINATING #-}
  SerializableSVec : ∀{a} → {A : Set a} → {{_ : Serializable A}} → Serializable (Σ Nat (λ x → Vec A x))
  encode ⦃ SerializableSVec ⦄ (zero , []) = empty
  encode ⦃ SerializableSVec ⦄ (suc n , x ∷ vs) =
    let nbs = encode x
    in (int64ToBS (length nbs) ~~ nbs) ~~ encode (n , vs)
  decode {{SerializableSVec}} x =
    let cs = do
               (pr , suf) ← splitAt 8 x
               ln ← bsToInt64 pr
               splitAt (int64ToNat ln) suf
    in case cs of λ { nothing → nothing ;
                      (just (bnb , rem)) → do
                                              (n , v) ← decode {{SerializableSVec}} rem
                                              vl ← decode bnb 
                                              return (suc n , (vl ∷ v))  }



  SerializableVec : ∀{a n} → {A : Set a} → {{_ : Serializable A}} → Serializable (Vec A n)
  encode ⦃ SerializableVec ⦄ [] = empty
  encode ⦃ SerializableVec ⦄ (x ∷ vs) =
    let nbs = encode x
    in (int64ToBS (length nbs) ~~ nbs) ~~ encode vs
  decode ⦃ SerializableVec {n = zero} ⦄ x = case (int64ToNat (length x)) of λ { zero → just [] ; (suc x) → nothing}
  decode ⦃ SerializableVec {n = suc n} {A}⦄ x = decode {{SerializableSVec {A = A}}} x >>= λ {(x , res) → case (x == suc n) of λ { (yes refl) → just res ;
                                                                                                                                   (no _) → nothing}}
