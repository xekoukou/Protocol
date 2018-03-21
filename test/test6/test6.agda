module test.test6.test6 where


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



g : PF cr Nat (constS Nat) tm cr
(_<l_ g) z = 2



test : ⊤
test = unit



check : ⊤ 
check = typeCheck g
