module test.test4.test4 where


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



e : PF cr Nat (constS Nat) tm cr
(_<l_ e) x = x

f : Nat → PF cr Nat (constS Nat) tm cr
f n = e

g : PF cr Nat (constS Nat) tm cr
g = f (e <l 2)



test : ⊤
test = unit



check : ⊤ 
check = typeCheck g
