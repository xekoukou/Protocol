module Test where


open import Prelude.IO
open import Prelude.Unit
open import Prelude.Monad
open import Prelude.String
open import Prelude.Product
open import Prelude.List
open import Prelude.Vec
open import Prelude.Bool

open import Protocol
open import Reflect

open import Tactic.Reflection

open import Prelude.Nat
open import Prelude.Semiring

data RoleA : Set where
  ar : RoleA
  br : RoleA
  cr : RoleA


tm : Timeout
tm = (timeout 4 0 0 0 0)

fun2 : CPF cr ⊤ (constS Nat) (timeout 4 0 0 0 0) cr
_<l_ fun2 x = 3
rl fun2 = LocalFun

module prot1 (r : RoleA) {{f : CPF ar ⊤ (constS Nat) (timeout 4 0 0 0 0) r}}
                         {{g : CPF br Nat (λ x → Vec Nat x) (timeout 4 0 0 0 0) r}}
                         {{e : CPF cr (Σ Nat (λ n → Vec Nat n)) {{sa = SerializableSVec}} (constS Nat) (timeout 4 0 0 0 0) r}}
                         where

  fun1 : CPF cr ⊤ (constS Nat) (timeout 4 0 0 0 0) r
  _<l_ fun1 x = let r = f <l x in e <l (r , g <l r)
  rl fun1 = RoleA
 


module prot2 (r : RoleA) {{f : CPF ar ⊤ (λ _ → Nat) tm r}}
                           {{g : CPF br ⊤ (λ _ → Nat) tm r}}
                           {{e : CPF cr (Nat × Nat × Nat) (λ _ → Nat) tm r}} where



  prot_rec2 : CPF cr Nat (λ _ → Nat) tm r
  (_<l_ prot_rec2) zero = e <l ((f <l unit) , (g <l unit) , 0)
  (_<l_ prot_rec2) (suc n) = e <l ((f <l unit) , (g <l unit) , prot_rec2 <l n)
  rl prot_rec2 = RoleA


  ro : CPF ar ⊤ (λ _ → Nat) tm r
  (_<l_ ro) s = g <l s
  rl ro = RoleA


open prot2



e : PF cr (Nat × Nat × Nat) (λ _ → Nat) tm cr
_<l_ e (0 , snd , thd) = snd + thd
_<l_ e (suc fst , snd , thd) = fst + snd + thd
-- rl e = {!!}

-- b : Bool → PF cr Nat (constS Nat) tm cr
-- b false = prot_rec2 cr {{e = e}}
-- b true = prot_rec2 cr {{e = e}}

-- g : PF cr Nat (constS Nat) tm cr
-- g = b true





-- -- test : (r : String) → String
-- -- test s = "hello"

-- -- tost : String
-- -- tost = "hell"


-- -- internalError : {A : Set} → Term → TC A
-- -- internalError term = typeError (strErr "This is an internal error. Please report it. Term :" ∷ termErr term ∷ [])

-- -- nextPi : Term → TC ((Arg Type) × Type)
-- -- nextPi term@(var x args) =  internalError term
-- -- nextPi term@(con c args) =  internalError term
-- -- nextPi term@(def f args) =  internalError term
-- -- nextPi term@(lam v t) =  internalError term
-- -- nextPi term@(pat-lam cs args) =  internalError term
-- -- nextPi (pi a (abs s x)) = return (a , x)
-- -- nextPi term@(agda-sort s) =  internalError term
-- -- nextPi term@(lit l) =  internalError term
-- -- nextPi term@(meta x x₁) =  internalError term
-- -- nextPi term@unknown = internalError term


-- -- visibleRoleError : {A : Set} → Term → TC A
-- -- visibleRoleError term = typeError (strErr "The role variable must be visible." ∷ termErr term ∷ [])

-- -- -- It should not contain Arguments and it must be Visible. It must be a data type definition.
-- -- firstPi : Arg Term → TC ⊤
-- -- firstPi (arg (arg-info visible r) x) = return unit -- TODO check the definition.
-- -- firstPi (arg (arg-info hidden r) x) = visibleRoleError x
-- -- firstPi (arg (arg-info instance′ r) x) = visibleRoleError x

-- -- typeIsCorrect' : Term → TC ⊤
-- -- typeIsCorrect' term =
-- --   do
-- --     (a , term) ← nextPi term
-- --     firstPi a
-- --     return unit    -- Continue the typechecking.
 
-- -- macro 
-- --   typeIsCorrect : Name → Tactic
-- --   typeIsCorrect nm hole =
-- --     do
-- --       t ← getType nm
-- --       s ← quoteTC tost
-- --       typeIsCorrect' t
-- --       unify hole s
  


-- -- fun : Nat → Nat → Nat → Nat
-- -- fun x y n =  x + (λ z → y + x + z) n

-- -- main : IO ⊤
-- -- main = do
-- --          putStr ("\nprotocol : \n" & reflectDef prot_rec2)
-- --          putStr ("\n\n")
-- --          putStr ("local function : \n" & reflectRedDef g)
-- --          putStr ("\n\n")
-- --          putStr (typeIsCorrect test)
