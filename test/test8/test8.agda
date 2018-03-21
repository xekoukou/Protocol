module test.test8.test8 where


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

postulate
  e : PF cr Nat (constS Nat) tm cr

g : Nat → PF cr Nat (constS Nat) tm cr
g (suc n) = e
g bob = e



test : ⊤
test = unit



check : ⊤ 
check = typeCheck g
