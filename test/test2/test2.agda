module test.test2.test2 where


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
  instance
    _ : Serializable (PF cr Nat (λ _ → Nat) (timeout 4 0 0 0 0) ar)





g : PF cr (PF cr Nat (constS Nat) tm ar) (constS Nat) tm cr
(_<l_ g) z = z <l 2



e : PF cr (PF cr Nat (constS Nat) tm ar) (constS Nat) tm cr
e = g


test : ⊤
test = unit



check : ⊤ 
check = typeCheck e
