module TypeCheck where


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
open import Prelude.Ord
open import Prelude.Maybe
open import Prelude.Semiring
open import Container.Traversable

open import Protocol

-- Important We do not check that patterned lambdas are projections. they shouldn't at the moment.



isConΣ : Name → Bool
isConΣ n = case (n == quote Prelude.Product.Σ) of λ { (yes x) → true ;
                                                      (no x) → false}

rmAbsCl : List Clause → List Clause
rmAbsCl [] = []
rmAbsCl (cl@(clause ps t) ∷ cls) = cl ∷ rmAbsCl cls
rmAbsCl (absurd-clause ps ∷ cls) = rmAbsCl cls

isFun<l : Name → Bool
isFun<l n = case (n == quote Protocol.PF._<l_) of λ { (yes x) → true ;
                                                      (no x) → false}

isFun? : Definition → TC (List Clause)
isFun? (function xs) = return (rmAbsCl xs)
isFun? x = typeError ((strErr "This is not a function.") ∷ [])


isProj? : Pattern → Bool
isProj? (proj f) = isFun<l f
isProj? x = false


foldt : ∀{a B} → {A : Set a} → List (Arg B) → (f : A → B → A) → A → A 
foldt xs f i = foldr (λ { (arg i x) y → f y x}) i xs


clToPtLen : Clause → Nat
clToPtLen (clause ps t) = length ps
clToPtLen (absurd-clause ps) = length ps

-- The Nat is the deBruijn index of the projection.
clToDb : Clause → Maybe Nat
clToDb (clause ps t) = do
                           (_ , n) ← (foldt ps (λ x y → do
                                                    (ps , db) ← x
                                                    ns ← return $ (isProj? y) || ps
                                                    ndb ← case (ns) of (λ { false → return 0 ;
                                                                            true → return $ suc db})
                                                    return (ns , ndb)  ) (return (false , 0)))
                           return n
clToDb (absurd-clause ps) = nothing 


clsToDbs : List Clause → List Nat
clsToDbs cls = foldr (λ x y → case (clToDb x) of (λ { nothing → y ; (just x) → x ∷ y})) [] cls

-- The Nat is the deBruijn index of the projection.
clToTerm : Clause → Maybe Term
clToTerm (clause ps t) = return t
clToTerm (absurd-clause ps) = nothing


clsToTerms : List Clause → List Term
clsToTerms cls = foldr (λ x y → case (clToTerm x) of (λ { nothing → y ; (just x) → x ∷ y})) [] cls


isItPFCon : ∀{ℓ} → {A : Set ℓ} → A → Name → TC A
isItPFCon r c = case (c == quote Protocol.PF.doNotUseThisConstructor) of
                                   λ { (no x) → return r ;
                                       (yes x) → typeError ((strErr "Use Copatterns instead of the Record Constructor, if you do not mind.") ∷ [])}









{-# NON_TERMINATING #-}
doWeHave<l : Term → TC Bool
doWeHave<l (var x args) = foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return false)
doWeHave<l (con c args) = foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return false)
doWeHave<l (def f args) = case (isFun<l f) of
  λ { false → foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return false) ;
      true → return true}
doWeHave<l (lit l) = return false
doWeHave<l unknown = return false
doWeHave<l (lam v (abs s x)) = doWeHave<l x
doWeHave<l (pat-lam cs args) =
  do
    tcs ← return $ clsToTerms cs
    t ← (foldr (λ x y → (do
                           py ← y
                           r ← doWeHave<l x
                           return $ r ||  py)) (return false) tcs)
    foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return t)
doWeHave<l x = typeError (strErr "It is not possible to return a Type or have a meta." ∷ termErr x ∷ [] )


returnedTypePF : Term → Bool
returnedTypePF (pi a (abs s x)) = returnedTypePF x
returnedTypePF (def f args) = case (f == quote Protocol.PF) of λ { (yes x) → true ; (no x) → false }
returnedTypePF x = false

-- 
-- -- Is this needed?
-- {-# NON_TERMINATING #-}
-- doWeHavePFCon : Term → TC Bool
-- doWeHavePFCon t =
--   do
--     t ← reduce t
--     case t of λ { (def f args) → (do
--                                     t ← getType f
--                                     return $ returnedTypePF t) ; 
--                   (con c args) → isItPFCon false c ;
--                   (lam v (abs s x)) → doWeHavePFCon x ;
--                   (pat-lam cs args) → {!!} ;
--                   x → return false}
-- 








performCheck1 : List Clause → TC (List Clause × List Bool × List Bool)
performCheck1 cls = foldr (λ { cl@(clause ps t) y →
                                                   (do
                                                      (cls , bprs , b<ls) ← y
                                                      b<l ← doWeHave<l t
                                                      bpr ← return $ (foldt ps (λ x y → x || isProj? y) false)
                                                      return (cl ∷ cls , bpr ∷ bprs , b<l ∷ b<ls)) ;
                                  (absurd-clause ps) y →  typeError ((strErr "This is an internal error, please report it.") ∷ [])}) (return ([] , [] , [])) cls


¬<l&¬proj : List Bool → List Bool → TC ⊤
¬<l&¬proj b<ls bprs = case foldr (λ x y → x || y) false $ zipWith (λ x y → x && (not y)) b<ls bprs of
                      λ { false → return unit ;
                          true → typeError ((strErr "A function has a clause that does not have a projection pattern, but its term contains a '<l' function.") ∷ []) }



-- ¬proj&PF : List Bool → List Bool → TC ⊤
-- ¬proj&PF bprs bfs = case foldr (λ x y → x || y) false $ zipWith (λ x y → x && y) bprs bfs of
--                       λ { false → return unit ;
--                           true → typeError ((strErr "A PF projection should not return a value of type PF.") ∷ []) }
-- 


rmUnknown : List (Arg Term) → List (Arg Term)
rmUnknown [] = []
rmUnknown (arg i unknown ∷ xs) = rmUnknown xs
rmUnknown (arg i x ∷ xs) = arg i x ∷ rmUnknown xs




{-# NON_TERMINATING #-}
noVarsBelowDB : Nat → Term → TC ⊤
noVarsBelowDB n (var x args) = case (x <? n) of λ { false → foldt args (λ x y → noVarsBelowDB n y) (return unit) ;
                                                    true → typeError ((strErr "A variable that is part of the domain of <l is used in a function that only accepts metavariables, compile time variables.") ∷ [])}
noVarsBelowDB n (con c args) = foldt args (λ x y → noVarsBelowDB n y) (return unit)
noVarsBelowDB n (def f args) = foldt args (λ x y → noVarsBelowDB n y) (return unit)
noVarsBelowDB n (lam v (abs s x)) = noVarsBelowDB (suc n) x
noVarsBelowDB n (pat-lam cs args) =
  do
    tcs ← return (clsToTerms cs)
    lens ← return $ map clToPtLen cs
    foldr (λ x y → let px = fst x ; len = snd x in noVarsBelowDB (n + len) px) (return unit) (zip tcs lens)
    foldt args (λ x y → noVarsBelowDB n y) (return unit)
noVarsBelowDB n x = return unit


constrains : Nat → List (Arg Term) → TC ⊤
constrains db args = do
                       foldt args (λ x y → noVarsBelowDB db y) (return unit)
                       caseM (foldt args (λ x y → do l ← doWeHave<l y ; r ← x ; return (r || l) ) (return false)) of
                         λ { false → return unit ;
                             true → typeError ((strErr "A meta function cannot have in its args the <l function.") ∷ [])}



{-# NON_TERMINATING #-}
performCheck2 : Nat → Term → TC ⊤
performCheck2 db (var x args) = case (x >? db) of
                                  λ { true → constrains db args ;
                                      false → return unit}
performCheck2 db (con c args) = do
                                  case (isConΣ c) of (λ { false → constrains db args ;
                                                          true → return unit})
                                  foldt args (λ x y → performCheck2 db y) (return unit)
performCheck2 db (def f args) = do
                                  case (isFun<l f) of
                                    λ { false → constrains db args ;
                                        true → return unit}
                                  foldt args (λ x y → performCheck2 db y) (return unit)
-- In both cases, DeBruijn needs to be changed to +1 for lam
-- and +k for pat lam where k is the number of args of pat-lam.
performCheck2 db (lam v (abs _ t)) = performCheck2 (suc db) t
performCheck2 db (pat-lam cs args) =
  do
    tcs ← return (clsToTerms cs)
    lens ← return $ map clToPtLen cs
    foldr (λ x y → let px = fst x ; len = snd x in performCheck2 (db + len) px) (return unit) (zip tcs lens)
    constrains db args
performCheck2 db (lit l) = return unit
performCheck2 db unknown = return unit
performCheck2 db x = typeError ((strErr "This is an internal error, please report it.") ∷ [])



checkPFType : Name → TC Bool
checkPFType nm =
  do
    ty ← getType nm
    rty ← reduce ty
    return (returnedTypePF rty)


mayProd : {A B : Set} → List (Maybe A × Maybe B) → List (A × B)
mayProd [] = []
mayProd ((nothing , snd) ∷ mls) = mayProd mls
mayProd ((just x , nothing) ∷ mls) = mayProd mls
mayProd ((just x , just y) ∷ mls) = (x , y) ∷ mayProd mls


typeCheckS : Name → TC ⊤
typeCheckS nm =
  do
    t ← getDefinition nm
    cls ← isFun? t
    (cls , bprs , b<ls) ← performCheck1 cls
    ¬<l&¬proj b<ls bprs
    -- prjs represent the case where we have a projection and it is not a local function.
    prjs ← return $ mayProd $ map (λ x → let cl = fst x in  (clToDb cl , clToTerm cl) ) $ filter (λ x → (fst (snd x)) && (snd (snd x))) (zip cls (zip bprs b<ls))
    foldr (λ x x₁ →
        let db = fst x 
            t = snd x in
        performCheck2 db t) (return unit) prjs



{-# NON_TERMINATING #-}
findAllNames : Term → List Name
findAllNames (var x args) = foldt args (λ x y → let nl = findAllNames y in nl ++ x) []
findAllNames (con c args) = foldt args (λ x y → let nl = findAllNames y in nl ++ x) []
findAllNames (def f args) = f ∷ foldt args (λ x y → let nl = findAllNames y in nl ++ x) []
findAllNames (lam v (abs _ t)) = findAllNames t
findAllNames (pat-lam cs args) = (foldr (_++_) [] $ map findAllNames (clsToTerms cs)) ++ foldt args (λ x y → let nl = findAllNames y in nl ++ x) []
findAllNames x = []


--    checkPFType nm

{-# NON_TERMINATING #-}
findAllNamesRec : List Name → Name → TC (List Name)
findAllNamesRec pl nm =
  do
    d ← getDefinition nm
    cls ← isFun? d
    nms ← return $ foldr (_++_) [] $ map findAllNames (clsToTerms cls)
    fnms ← foldr (λ x y → do caseM (checkPFType x) of λ { false → y ; true → do y ← y ; return (x ∷ y)}) (return []) nms
    ffnms ← return $ foldr (λ x y → case (all? (λ z → isNo $ x == z) y) of λ { true → x ∷ y ; false → y}) [] fnms
    newNms ← return $ filter (λ x → all? (λ z → isNo $ x == z) pl) ffnms
    prevNms ← return $ pl ++ newNms
    res ← foldr (λ x y → do (py , pnms) ← y ; nms ← findAllNamesRec py x ; return ((py ++ nms) , pnms ++ nms)) (return (prevNms , newNms)) newNms
    return $ snd res

macro
  typeCheck : Name → Term → TC ⊤
  typeCheck nm hole =
    do
      nms ← findAllNamesRec [] nm
      foldr (λ x y → typeCheckS x) (return unit) nms
      u ← quoteTC {A = ⊤} unit
      unify hole u
