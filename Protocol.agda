module Protocol where


open import Agda.Primitive
open import Serialize public



-- To be erased
postulate
  eraseMe : ∀{ℓ} → {A : Set ℓ} → A



-- These are used to differentiate them from the original version. This is to be dealt differently than the other version.

infixr 1 _,_
record Σₙ {a b} (A : Set a) (B : A → Set b) : Set (a ⊔ b) where
  no-eta-equality
  constructor _,_
  field
    fst : A
    snd : B fst

open Σₙ public

infixr 3 _×ₙ_
_×ₙ_ : ∀ {a b} → Set a → Set b → Set (a ⊔ b)
A ×ₙ B = Σₙ A (λ _ → B)




instance

  SerializableNProduct : ∀{a b} → {A : Set a} → {B : A → Set b} → {{ _ : Serializable A}}
                        → {{_ : {x : A} → Serializable (B x)}} → Serializable (Σₙ A B)
  encode {{SerializableNProduct}} = eraseMe
  decode {{SerializableNProduct}} = eraseMe





record PF {a b} {Role : Set} (r : Role) (A : Set a) (B : A → Set b)
          {{_ : Serializable A}} {{_ : {x : A} → Serializable (B x)}} (vr : Role) : Set (a ⊔ b) where
  field
    _<l_ : (x : A) → B x

open PF public

