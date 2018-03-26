module Protocol where


open import Agda.Primitive
open import Serialize public
open import Prelude.Nat
open import Prelude.Product
open import Prelude.Ord hiding (min)
open import Prelude.Semiring

-- To be erased
postulate
  eraseMe : ∀{ℓ} → {A : Set ℓ} → A



-- FIX THIS. Provide an implementation here.
instance

  SerializableNProduct : ∀{a b} → {A : Set a} → {B : A → Set b} → {{ _ : Serializable A}}
                        → {{_ : {x : A} → Serializable (B x)}} → Serializable (Σ A B)
  encode {{SerializableNProduct}} = eraseMe 
  decode {{SerializableNProduct}} = eraseMe





record Timeout : Set where
  constructor timeout
  field
    ms : Nat
    s : Nat
    min : Nat
    hour : Nat
    day : Nat



module _ where

  open Timeout
  
  data _≤ₜ_ (a b : Timeout) : Set where
    ineq : ms a + (s a * 1000) + (min a * 60 * 1000) + (hour a * 60 * 60 * 1000) + (hour a * 24 * 60 * 60 * 1000) < ms b + (s b * 1000) + (min b * 60 * 1000) + (hour b * 60 * 60 * 1000) + (hour b * 24 * 60 * 60 * 1000) → a ≤ₜ b

postulate
  LocalFun : Set

data AgentConnInfo : Set where

record Context (Role : Set) : Set₁ where
  field
    ctx : (Role → AgentConnInfo)

postulate
  instance
    LContest : Context LocalFun

-- The context is derivable.
record PF {a b} {Role : Set} (r : Role) (A : Set a) {{sa : Serializable A}} (B : A → Set b)
          {{sb : {x : A} → Serializable (B x)}} (t : Timeout) (vr : Role) : Set (lsuc a ⊔ b) where
  constructor doNotUseThisConstructor
  field
    _<l_ : (x : A) → B x
    rl : Set
    {{ctx}} : Context rl

open PF public



-- Can I use postulates here? Probably not.
instance
  unPF : ∀{a b} {Role : Set} {r : Role} {A : Set a} {{sa : Serializable A}} {B : A → Set b}
          {{sb : {x : A} → Serializable (B x)}} {t : Timeout} {vr : Role} → PF r A B t vr
  unPF = eraseMe

---- This is created to have an instance error.
  pF : ∀{a b} {Role : Set} {r : Role} {A : Set a} {{sa : Serializable A}} {B : A → Set b}
          {{sb : {x : A} → Serializable (B x) }} {t : Timeout} → PF r A B t r
  pF ._<l_ x = eraseMe
  rl pF = eraseMe
  ctx pF = eraseMe



CPF : ∀{a b} {Role : Set} (r : Role) (A : Set a) {{sa : Serializable A}} (B : A → Set b) {{sb : {x : A} → Serializable (B x)}} (t : Timeout) (vr : Role) → Set (lsuc a ⊔ b)
CPF {_} {_} {Role} r A B t vr = {{ctx : Context Role}} → PF r A B t vr

DCPF : ∀{a b} (DRole : Set) {Role : Set} (r : Role) (A : Set a) (B : A → Set b) (t : Timeout) (vr : Role) → Set (lsuc a ⊔ b)
DCPF {_} {_} DRole {Role} r A B t vr = {{ctx : Context DRole}} {{sa : Serializable A}} {{sb : {x : A} → Serializable (B x)}} → PF r A B t vr

constS : ∀{a b} → {A : Set a} → (B : Set b) → (A → Set b)
constS B = λ _ → B




-- This should not be permitted with this iteration of PF. It may still be helpfull though.
cproj : ∀{a b} → {A : Set a} → {B : Set b} → Σ A (constS B) → B
cproj (fst , snd) = snd





---------------------

open import Prelude.Equality
open import Prelude.Empty


embed : ∀{a b} {RA RB : Set} {r : RA} {A : Set a} {{sa : Serializable A}} {B : A → Set b}
      {{sb : {x : A} → Serializable (B x)}} {t : Timeout} {vr : RA} → {rb : RB} → PF rb A B t rb → PF r A B t vr
_<l_ (embed pf) = _<l_ pf
rl (embed pf) = rl pf
ctx (embed pf) = ctx pf


