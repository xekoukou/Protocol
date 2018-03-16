module test1 where


open import Prelude.String
open import Prelude.Unit

open import Protocol
open import TypeCheck


test : String
test = "ho"



check : ⊤
check = typeCheck test
