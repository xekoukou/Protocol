module test.test9.test9 where


open import Prelude.Unit
open import Prelude.Nat

open import TypeCheck


g : Nat → Nat
g (suc n) = zero
g bob = zero



test : ⊤
test = unit



check : ⊤ 
check = typeCheck g
