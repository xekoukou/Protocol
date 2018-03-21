module test.test5.test5 where


open import Prelude.Unit


open import Prelude.Nat
open import Prelude.Semiring
open import Prelude.Vec
open import Prelude.Bool
open import Prelude.Product


open import Protocol
open import TypeCheck


bol : Nat → Nat 
bol x = suc x


data RoleA : Set where
  ar : RoleA
  br : RoleA
  cr : RoleA


tm : Timeout
tm = (timeout 4 0 0 0 0)

e : PF cr Nat (constS Nat) tm ar
(_<l_ e) x = x

g : PF cr Nat (constS Nat) tm cr
(_<l_ g) x = bol (e <l x)

f : PF cr Nat (constS Nat) tm cr
f = g

test : ⊤
test = unit



check : ⊤ 
check = typeCheck f
