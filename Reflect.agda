module Reflect where


open import Prelude.Monad
open import Prelude.Show
open import Prelude.IO
open import Prelude.Nat
open import Prelude.Unit
open import Prelude.List hiding (_++_)
open import Data.String hiding (show)
open import Tactic.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Nat.Reflect
open import Tactic.Deriving.Eq
open import Agda.Builtin.List
open import Prelude.Bool

postulate
  error : ∀{ℓ} → {A : Set ℓ} → String → A

{-# COMPILE GHC error = (\_ _ x -> error (Data.Text.unpack x)) #-} 

instance
  ShowArg : ∀{A} → {{ShowA : Show A}} → Show (Arg A)
  ShowArg = simpleShowInstance λ { (arg i x) → "Arg " ++ show x}

mutual
--  For the moment, we ignore ArgInfo
  showArgTermn : Nat → Arg Term → String
  showArgTermn zero (arg i x) = ""
  showArgTermn (suc n) (arg i x) = showTermn n x

  showArgTerms : Nat → List (Arg Term) → String
  showArgTerms n args = "[ " ++ foldr (λ arg s → showArgTermn n arg ++ " , " ++ s) "]" args

  showTermn : Nat → Term → String
  showTermn zero t = ""
  showTermn (suc n) (var x args) = "TRM( Var " ++ (show x) ++ " " ++ showArgTerms n args ++ " )"
  showTermn (suc n) (con c args) = "TRM( Con " ++ show c ++ " "  ++ showArgTerms n args ++ " )"
  showTermn (suc n) (def f args) = "TRM( Def " ++ show f ++ " " ++ showArgTerms n args ++ " )"
  showTermn (suc n) (lam v (abs s x)) = "TRM( Lam (abs " ++ s ++ " " ++ showTermn n x ++ " )" ++ " )"
  showTermn (suc n) (pat-lam cs args) = "TRM( Pat-lam " ++ "?Clauses? " ++ showArgTerms n args ++ " )"
  showTermn (suc n) (pi a (abs s b)) = "TRM( Pi " ++ showArgTermn n a ++ " (abs " ++ s ++ " " ++ showTermn n b ++ " )" ++ " )"
  showTermn (suc n) (agda-sort s) = "TRM( ?Agda-Sort?" ++ " )"
  showTermn (suc n) (lit l) = "TRM( Lit " ++ show l ++ " )"
  showTermn (suc n) (meta x x₁) = "TRM( Meta " ++ "?meta? " ++ showArgTerms n x₁  ++ " )"
  showTermn (suc n) unknown = "TRM( Unknown" ++ " )"


showTerm : Term → String
showTerm t = showTermn 100000000 t



instance
  ShowTerm : Show Term
  ShowTerm = simpleShowInstance showTerm

mutual

  showArgPtn : Nat → Arg Pattern → String
  showArgPtn zero (arg i x) = ""
  showArgPtn (suc n) (arg i x) = showPatternn n x

  showArgPts : Nat → List (Arg Pattern) → String
  showArgPts n args = foldr (λ arg s → s ++ " , " ++ showArgPtn n arg) "[" args ++ " ]"

  showPatternn : Nat → Pattern → String
  showPatternn zero pt = ""
  showPatternn (suc n) (con c ps) = "  PT( Con " ++ show c ++ " " ++ showArgPts n ps ++ " )"
  showPatternn (suc n) dot = "  PT( Dot" ++ " )"
  showPatternn (suc n) (var s) = "  PT( Var " ++ s ++ " )"
  showPatternn (suc n) (lit l) = "  PT( Lit " ++ show l ++ " )"
  showPatternn (suc n) (proj f) = "  PT( Proj " ++ show f ++ " )"
  showPatternn (suc n) absurd = "  PT( Absurd" ++ " )"

showPattern : Pattern → String
showPattern pt = showPatternn 10000000 pt


instance
  ShowPattern : Show Pattern
  ShowPattern = simpleShowInstance showPattern


showClause : Clause → String
showClause (clause ps t) = "\n\nCl Clause " ++ show ps ++ " " ++ show t
showClause (absurd-clause ps) = "\n\nCl Absurd-Clause " ++ show ps

instance
  ShowClause : Show Clause
  ShowClause = simpleShowInstance showClause

showDef : Definition → String
showDef (function cs) = "Def( Function " ++ show cs ++ " )"
showDef (data-type pars cs) = "Def( Data-Type " ++ show pars ++ " " ++ show cs ++ " )"
showDef (record-type c fs) = "Def( Record-Type " ++ show fs ++ " )"
showDef (data-cons d) = "Def( Data-Cons " ++ show d ++ " )"
showDef axiom = "Def( Axiom" ++ " )"
showDef prim-fun = "Def( Prim-Fun" ++ " )"



macro

  reflectType : Name → Tactic
  reflectType nm hole =
    do
      t ← getType nm
      s ← quoteTC (showTerm t)
      unify hole s

  reflectDef : Name → Tactic
  reflectDef nm hole =
    do
      t ← getDefinition nm
      s ← quoteTC (showDef t)
      unify hole s



-- -- The first pattern is the role, the second the deconstructed value and the rest are the NF functions.
-- pmC : Clause → Clause
-- pmC (clause ps t) = {!!}
-- pmC (absurd-clause ps) = absurd-clause ps

-- pmF : Definition → Definition
-- pmF (function cs) = function (map pmC cs)
-- pmF _ = error "This function only takes function definitions."

-- typeIsCorrect : Type → Bool
-- typeIsCorrect (var x args) = {!!}
-- typeIsCorrect (con c args) = {!!}
-- typeIsCorrect (def f args) = {!!}
-- typeIsCorrect (lam v t) = {!!}
-- typeIsCorrect (pat-lam cs args) = {!!}
-- typeIsCorrect (pi a (abs s x)) = {!!}
-- typeIsCorrect (agda-sort s) = {!!}
-- typeIsCorrect (lit l) = {!!}
-- typeIsCorrect (meta x x₁) = {!!}
-- typeIsCorrect unknown = {!!}
