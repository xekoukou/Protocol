module Reflect where


open import Prelude.Monad
open import Prelude.Show
open import Prelude.IO
open import Prelude.Nat
open import Prelude.Unit
open import Prelude.List
open import Prelude.String
open import Tactic.Reflection
open import Tactic.Reflection.Quote
open import Tactic.Nat.Reflect
open import Tactic.Deriving.Eq
open import Agda.Builtin.List
open import Prelude.Bool
open import Prelude.Function
open import Prelude.Equality
open import Prelude.Decidable
open import Prelude.Product
open import Container.Traversable

open import Protocol

-- To be erased
postulate
  IMPOSSIBLE : ∀{ℓ} → {A : Set ℓ} → A



postulate
  error : ∀{ℓ} → {A : Set ℓ} → String → A

{-# COMPILE GHC error = (\_ _ x -> error (Data.Text.unpack x)) #-} 

instance
  ShowArg : ∀{A} → {{ShowA : Show A}} → Show (Arg A)
  ShowArg = simpleShowInstance λ { (arg i x) → "Arg " & show x}

Tab : Set
Tab = Nat


nspace : Tab → String
nspace zero = ""
nspace (suc tb) = "  " & (nspace tb) 

mutual
--  For the moment, we ignore ArgInfo
  showArgTermn : Nat → Tab → Arg Term → String
  showArgTermn zero tb (arg i x) = ""
  showArgTermn (suc n) tb (arg i x) = showTermn n tb x

  showArgTerms : Nat → Tab → List (Arg Term) → String
  showArgTerms n tb args = "[ " & foldr (λ arg s → "\n" & showArgTermn n tb arg & s) "]" args

  showTermn : Nat → Tab → Term → String
  showTermn zero tb t = ""
  showTermn (suc n) tb (var x args) = nspace tb & "TRM( Var " & (show x) & " " & showArgTerms n (suc tb) args & " )"
  showTermn (suc n) tb (con c args) = nspace tb & "TRM( Con " & show c & " "  & showArgTerms n (suc tb) args & " )"
  showTermn (suc n) tb (def f args) = nspace tb & "TRM( Def " & show f & " " & showArgTerms n (suc tb) args & " )"
  showTermn (suc n) tb (lam v (abs s x)) = nspace tb & "TRM( Lam (abs " & s & "\n" & showTermn n (suc tb) x & " )" & " )"
  showTermn (suc n) tb (pat-lam cs args) = nspace tb & "TRM( Pat-lam " & "?Clauses? " & showArgTerms n (suc tb) args & " )"
  showTermn (suc n) tb (pi a (abs s b)) = nspace tb & "TRM( Pi " & showArgTermn n tb a & "\n" & (nspace tb) & "(abs " & s & " \n" & showTermn n (suc tb) b & " )" & " )"
  showTermn (suc n) tb (agda-sort s) = nspace tb & "TRM( ?Agda-Sort?" & " )"
  showTermn (suc n) tb (lit l) = nspace tb & "TRM( Lit " & show l & " )"
  showTermn (suc n) tb (meta x x₁) = nspace tb & "TRM( Meta " & "?meta? \n" & (nspace tb) & showArgTerms n (suc tb) x₁  & " )"
  showTermn (suc n) tb unknown = nspace tb & "TRM( Unknown" & " )"


showT : Term → Tab → String
showT t tb = showTermn 100000000 tb t




mutual

  showArgPtn : Nat → Tab → Arg Pattern → String
  showArgPtn zero tb (arg i x) = nspace tb & ""
  showArgPtn (suc n) tb (arg i x) = nspace tb & showPatternn n tb x

  showArgPts : Nat → Tab → List (Arg Pattern) → String
  showArgPts n tb args = foldr (λ arg s → "\n" & showArgPtn n tb arg & s) "[" args & " ]"

  showPatternn : Nat → Tab → Pattern → String
  showPatternn zero tb pt = nspace tb & ""
  showPatternn (suc n) tb (con c ps) = nspace tb & "  PT( Con " & show c & " " & showArgPts n (suc tb) ps & " )"
  showPatternn (suc n) tb dot = nspace tb & "  PT( Dot" & " )"
  showPatternn (suc n) tb (var s) = nspace tb & "  PT( Var " & s & " )"
  showPatternn (suc n) tb (lit l) = nspace tb & "  PT( Lit " & show l & " )"
  showPatternn (suc n) tb (proj f) = nspace tb & "  PT( Proj " & show f & " )"
  showPatternn (suc n) tb absurd = nspace tb & "  PT( Absurd" & " )"

showP : Pattern → Tab → String
showP pt tb = showPatternn 10000000 tb pt


showCl : Clause → Tab → String
showCl (clause ps t) tb = nspace tb & "Cl Clause " & showArgPts 10000000 (suc tb) ps & "\n" & showT t (suc tb)
showCl (absurd-clause ps) tb = nspace tb & "Cl Absurd-Clause " & showArgPts 10000000 (suc tb) ps

showCls : Tab → List Clause → String
showCls tb args = foldr (λ arg s → s & " , \n" & showCl arg tb) "[" args & " ]"

showDef : Definition → String
showDef (function cs) = "Def( Function " & showCls 1 cs & " )"
showDef (data-type pars cs) = "Def( Data-Type " & show pars & " " & show cs & " )"
showDef (record-type c fs) = "Def( Record-Type " & show fs & " )"
showDef (data-cons d) = "Def( Data-Cons " & show d & " )"
showDef axiom = "Def( Axiom" & " )"
showDef prim-fun = "Def( Prim-Fun" & " )"



-- In case a protocol is created from a function application, we need to reduce that function.
-- That is what we do here.
reduceTerm : Term → TC Term
reduceTerm t = reduce t

reduceCl : Clause → TC Clause
reduceCl (clause ps t) = do
                           x ← reduceTerm t
                           return $ clause ps x
reduceCl (absurd-clause ps) = return $ absurd-clause ps

reduceFunDef : Definition → TC Definition 
reduceFunDef (function cs) = do
                               x ← mapM reduceCl cs 
                               return $ function x
reduceFunDef x = typeError ((strErr "This macro is to be used on a function.") ∷ [])




macro

  reflectType : Name → Tactic
  reflectType nm hole =
    do
      t ← getType nm
      s ← quoteTC (showT t 0)
      unify hole s

  reflectDef : Name → Tactic
  reflectDef nm hole =
    do
      t ← getDefinition nm
      s ← quoteTC (showDef t)
      unify hole s


  reflectRedDef : Name → Tactic
  reflectRedDef nm hole =
    do
      t ← getDefinition nm
      rt ← reduceFunDef t
      s ← quoteTC (showDef rt)
      unify hole s





-- hasTypePF : Term → Bool
-- hasTypePF (pi a (abs s x)) = hasTypePF x
-- hasTypePF (def f args) = case (f == quote Protocol.PF) of λ { (yes x) → true ; (no x) → false }
-- hasTypePF x = false

-- isFun<l : Name → Bool
-- isFun<l n = case (n == quote Protocol.PF._<l_) of λ { (yes x) → true ;
--                                                       (no x) → false}

-- isConΣ : Name → Bool
-- isConΣ n = case (n == quote Prelude.Product.Σ) of λ { (yes x) → true ;
--                                                       (no x) → false}

-- -- We need to check whether there are <l applications and if there are PF definitions.
-- -- No result of <l should be used to construct PF definitions.
-- -- If we do not have <l, then we can either have a PF definition or a local function. in a WHNF. (after reduction)
-- -- if we have <l, then we only need to have applications of <l and nothing else.

-- foldt : ∀{a} → {A : Set a} → List (Arg Term) → (f : A → Term → A) → A → A 
-- foldt xs f i = foldr (λ { (arg i x) y → f y x}) i xs

-- isItPFCon : ∀{ℓ} → {A : Set ℓ} → A → Name → TC A
-- isItPFCon r c = case (c == quote Protocol.PF.doNotUseThisConstructor) of
--                                    λ { (yes x) → return r ;
--                                        (no x) → typeError ((strErr "Use Copatterns instead of the Record Constructor, if you do not mind.") ∷ [])}


-- -- IMPORTANT, the function _<l_ can be passed as an argument, we do not check for that yet. We need to check the patterns for that.
-- {-# NON_TERMINATING #-}
-- doWeHave<l : Term → TC Bool
-- doWeHave<l (var x args) = foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return false)
-- doWeHave<l (con c args) = foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return false)
-- doWeHave<l (def f args) = case (isFun<l f) of
--   λ { false → foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return false) ;
--       true → return true}
-- doWeHave<l (lit l) = return false
-- doWeHave<l unknown = return false
-- doWeHave<l (lam v (abs s x)) = doWeHave<l x
-- doWeHave<l (pat-lam cs args) =  foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return false)
-- doWeHave<l x = typeError (strErr "It is not possible to return a Type or have a meta." ∷ termErr x ∷ [] )


-- -- caseM (doWeHave<l (def f args)) of
-- --                                                    λ { false → return true  ;
-- --                                                        true → typeError ((strErr "One should only use '<l' when it constructs a PF. : " ∷ termErr t ∷ []))   }}); 

-- doWeHavePFCon : Term → TC Bool
-- doWeHavePFCon t =
--   do
--     t ← reduce t
--     case t of λ { (def f args) → (do
--                                     t ← getType f
--                                     return $ hasTypePF t) ; 
--                   (con c args) → isItPFCon false c ;
--                   x → return false}


-- {-# NON_TERMINATING #-}
-- conWithLit : Term → Bool
-- conWithLit (con c args) = foldt args (λ x y → x && (conWithLit y)) true 
-- conWithLit (lit l) = true
-- conWithLit unknown = true
-- conWithLit x = false -- typeError ((strErr "All Constructors ,except Σ, should only have literals as input.") ∷ [])

-- {-# NON_TERMINATING #-}
-- only<l : Term → Bool
-- only<l (var x args) = foldt args (λ x y → x && (only<l y)) true 
-- -- The only constructor that we should allow is Σ or constant values.
-- only<l (con c args) = case (isConΣ c) of λ { false → conWithLit (con c args) ; true → foldt args (λ x y → x && (only<l y)) true }
-- only<l (def f args) =  case (isFun<l f) of λ { false → false ; true → foldt args (λ x y → x && (only<l y)) true}
-- only<l (lit l) = true
-- only<l unknown = true
-- only<l x = false






-- last : ∀{a} → {A : Set a} → A → List A → A
-- last y [] = y
-- last y (x ∷ xs) = last x xs

-- data TF : Set where
--   lfun : TF
--   pcon : TF
--   proj : TF


-- allPForNone : List (Arg Pattern) → Bool
-- allPForNone [] = true
-- allPForNone (arg i (con c ps₁) ∷ ps) = {!!}
-- allPForNone ((arg i x) ∷ ps) = {!!}

-- tf?Pt : Arg Pattern → Bool
-- tf?Pt (arg i (proj f)) = case (f == quote Protocol._<l_) of λ { (yes x) → true ; (no x) → false}
-- tf?Pt (arg i x) = false

-- tf?Cl : Clause → TC TF
-- tf?Cl (clause [] t) = caseM (doWeHavePFCon t) of λ { false → typeError((strErr "This function has zero arguments and it does not return a PF function.") ∷ []) ; true → return pcon }
-- tf?Cl (clause aps@(x ∷ ps) t) = case (reverse aps) of
--   λ { [] → IMPOSSIBLE ;
--       (x ∷ xs) → case (tf?Pt x) of
--                    λ { false →  typeError ((strErr "This function does not construct a PF function.") ∷ []) ;
--                        true → {!!}}}
-- tf?Cl (absurd-clause []) =  typeError ((strErr "This is an internal error, please report it.") ∷ [])
-- tf?Cl (absurd-clause (x ∷ ps)) = case (tf?Pt $ last x ps) of
--   λ { false → typeError ((strErr "This function does not construct a PF function.") ∷ []) ;
--       true → return lfun} -- ????

-- tf? : Definition → TC TF
-- tf? (function []) = typeError ((strErr "This is an internal error, please report it.") ∷ [])
-- tf? (function [ x ]) = {!!}
-- tf? (function (x ∷ x1 ∷ cs)) = {!!}
-- tf? x = typeError ((strErr "This is not a function.") ∷ [])



-- typeCheck : Name → TC Bool
-- typeCheck nm =
--   do
--     t ← getDefinition nm
--     ty ← getType nm
--     {!!}




-- -- There are 3 cases. A <l takes inputs from other <l or from functions g. His PF argument does not have <l.
-- --- All functions g do not take input from <l or PF types or the var after the projection.
-- --- Thus we need to check the types of the arguments.

-- -- If there are no <l, then this is a local function, and anything goes.

-- --- Secondly a function that constructs a PF does not have input from <l but it can and should have args with type PF.


-- -- In the first case, we have a function with projection pattern.
-- -- In the second case, we do not have a projection pattern, bu we return a PF type.
