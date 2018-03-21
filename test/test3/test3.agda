module test.test3.test3 where


open import Prelude.Unit


open import Prelude.Nat
open import Prelude.Semiring
open import Prelude.Vec
open import Prelude.Bool
open import Prelude.Product


open import Protocol
open import TypeCheck


data RoleA : Set where
  ar : RoleA
  br : RoleA
  cr : RoleA


tm : Timeout
tm = (timeout 4 0 0 0 0)


f : PF cr Nat (constS Nat) tm cr
f = doNotUseThisConstructor (λ x → zero)

test : ⊤
test = unit



check : ⊤ 
check = typeCheck f
