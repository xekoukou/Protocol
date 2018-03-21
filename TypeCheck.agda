module TypeCheck where


open import Prelude.Monad
open import Prelude.Show
open import Prelude.IO
open import Prelude.Nat
open import Prelude.String
open import Prelude.Unit
open import Prelude.List
open import Tactic.Reflection
open import Tactic.Reflection.Equality
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
open import Prelude.Sum
open import Prelude.Maybe
open import Prelude.Semiring
open import Container.Traversable

open import Protocol

open import Reflect

-- Important We do not check that patterned lambdas are (<l). they shouldn't at the moment.
-- Are pat-lam local function ? thus impossible to be (<l). I doubt it.



isConΣ : Name → Bool
isConΣ n = case (n == quote Prelude.Product.Σ._,_) of λ { (yes x) → true ;
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

-- The Nat is the deBruijn limit. Equal or greater are metavariables.
clToDb : Clause → Maybe Nat
clToDb (clause ps t) = do
                           (_ , n) ← (foldt ps (λ x y → do
                                                    (ps , db) ← x
                                                    ns ← return $ (isProj? y) || ps
                                                    ndb ← case (ns) of (λ { false → return (suc db) ;
                                                                            true → return db })
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









{-# TERMINATING #-}
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
-- {-# TERMINATING #-}
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
                                  (absurd-clause ps) y →  typeError ((strErr "This is an internal error, please report it. 8") ∷ [])}) (return ([] , [] , [])) cls


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




{-# TERMINATING #-}
noVarsBelowDB : Nat → Term → TC ⊤
noVarsBelowDB n (var x args) = case (x ≤? n) of λ { false → foldt args (λ x y → noVarsBelowDB n y) (return unit) ;
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



{-# TERMINATING #-}
performCheck2 : Nat → Term → TC ⊤
performCheck2 db (var x args) = do
                                  case (x >? db) of
                                    λ { true → constrains db args ;
                                        false → do
                                                  mapM (λ {(arg i y) → performCheck2 db y}) args
                                                  return unit }
performCheck2 db (con c args) = do
                                  debugPrint "prfCh2" 9 ((strErr ("Constructor name : " & show c)) ∷ [])
                                  case (isConΣ c) of
                                    (λ { false → constrains db args ;
                                         true → do
                                                  mapM (λ {(arg i y) → performCheck2 db y}) args
                                                  return unit })
                                  
performCheck2 db (def f args) = do
                                  debugPrint "prfCh2" 9 ((strErr ("Function name : " & show f)) ∷ [])
                                  case (isFun<l f) of
                                    λ { false → constrains db args ;
                                        true → do
                                                  mapM (λ {(arg i y) → performCheck2 db y}) args
                                                  return unit }
                                  
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
performCheck2 db x = typeError ((strErr "This is an internal error, please report it. 9") ∷ [])


-- A : Data from the network cannot be the first arg of a <l function.
{-# TERMINATING #-}
performCheck3 : Nat → Term → TC ⊤
performCheck3 db (var x args) =
  do
    mapM (λ {(arg i y) → performCheck3 db y}) args
    return unit
performCheck3 db (con c args) =
  do
    mapM (λ {(arg i y) → performCheck3 db y}) args
    return unit
performCheck3 db (def f args) =
  do
    mapM (λ {(arg i y) → performCheck3 db y}) args
    case (isFun<l f) of
      (λ { false → return unit ;
           true → case (rmUnknown args) of
                    λ { [] → typeError ((strErr "Internal Error. Please report it. 1") ∷ []) ;
                        (arg i (var x _) ∷ x₁) → case x <? db of
                                                   λ { false → return unit ;
                                                       true → typeError ((strErr "We cannot send PF typed data through the network.") ∷ [])} ;
                        (arg i x ∷ x₁) → typeError ((strErr "Internal Error. Please report it. 2") ∷ [])}})
performCheck3 db (lam v (abs _ x)) = performCheck3 (suc db) x
performCheck3 db (pat-lam cs args) =
  do
    tcs ← return (clsToTerms cs)
    lens ← return $ map clToPtLen cs
    foldr (λ x y → let px = fst x ; len = snd x in performCheck3 (db + len) px) (return unit) (zip tcs lens)
    foldt args (λ x y → performCheck3 db y) (return unit)
performCheck3 db x = return unit


checkPFType : Name → TC Bool
checkPFType nm =
  do
    debugPrint "chpf" 9 (strErr ("checkPFTypeName : " & show nm ) ∷ [])
    ty ← getType nm
    debugPrint "chpf" 9 (strErr ("Type : " ) ∷ (termErr ty) ∷ [])
    return (returnedTypePF ty)  --rty



{-# TERMINATING #-}
onlyCoPatterns : Term → TC ⊤
onlyCoPatterns (var x args) = do
                                mapM (λ {(arg i y) → onlyCoPatterns y}) args
                                return unit
onlyCoPatterns (con c args) = do
                                mapM (λ {(arg i y) → onlyCoPatterns y}) args
                                isItPFCon unit c
onlyCoPatterns (def f args) = do
                                mapM (λ {(arg i y) → onlyCoPatterns y}) args
                                return unit
onlyCoPatterns (lam v (abs _ t)) = onlyCoPatterns t
onlyCoPatterns (pat-lam cs args) =
  do
    tcs ← return (clsToTerms cs)
    mapM (λ y → onlyCoPatterns y) tcs
    mapM (λ {(arg i y) → onlyCoPatterns y}) args
    return unit
onlyCoPatterns (lit l) = return unit
onlyCoPatterns unknown = return unit
onlyCoPatterns x =  typeError ((strErr "Internal error, report it 10") ∷ [])



mayProd : {A B : Set} → List (Maybe A × Maybe B) → List (A × B)
mayProd [] = []
mayProd ((nothing , snd) ∷ mls) = mayProd mls
mayProd ((just x , nothing) ∷ mls) = mayProd mls
mayProd ((just x , just y) ∷ mls) = (x , y) ∷ mayProd mls


typeCheckS : Name → TC ⊤
typeCheckS nm =
  do
    debugPrint "tychS" 9 (strErr ("Name : \n" & show nm) ∷ [])
    ty ← getType nm
    t ← getDefinition nm
    cls ← isFun? t
    (cls , bprs , b<ls) ← performCheck1 cls
    debugPrint "tychS" 9 (strErr ("PerformCheck1 : \n" & showCls 5 cls & "\n     " & show (bprs , b<ls)) ∷ [])
    ¬<l&¬proj b<ls bprs
    mapM onlyCoPatterns (clsToTerms cls)
    -- prjs represent the case where we have a projection and it is not a local function.
    prjs ← return $ mayProd $ map (λ x → let cl = fst x in  (clToDb cl , clToTerm cl) ) $ filter (λ x → (fst (snd x)) && (snd (snd x))) (zip cls (zip bprs b<ls))
    debugPrint "tychS" 9 (strErr ("Protocols : \n" & show (length prjs)) ∷ [])
    mapM (λ x →
        let db = fst x 
            t = snd x in
        do    
          debugPrint "tychS" 9 (strErr ("PerformCheck2 db: " & show db) ∷ [])
          performCheck2 db t
          performCheck3 db t) prjs
    return unit



{-# TERMINATING #-}
findAllNames : Term → List Name
findAllNames (var x args) = foldt args (λ x y → let nl = findAllNames y in nl ++ x) []
findAllNames (con c args) = foldt args (λ x y → let nl = findAllNames y in nl ++ x) []
findAllNames (def f args) = f ∷ foldt args (λ x y → let nl = findAllNames y in nl ++ x) []
findAllNames (lam v (abs _ t)) = findAllNames t
findAllNames (pat-lam cs args) = (foldr (_++_) [] $ map findAllNames (clsToTerms cs)) ++ foldt args (λ x y → let nl = findAllNames y in nl ++ x) []
findAllNames x = []


--    checkPFType nm

{-# TERMINATING #-}
findAllNamesRec : List Name → Name → TC (List Name)
findAllNamesRec pl nm =
  do
    debugPrint "fndR" 9 (strErr ("Name : " & show nm) ∷ [])
    d ← getDefinition nm
    cls ← isFun? d
    nms ← return $ foldr (_++_) [] $ map findAllNames (clsToTerms cls)
    debugPrint "fndR" 9 (strErr ("Names : " & show nms) ∷ [])
    fnms ← foldr (λ x y → do caseM (checkPFType x) of λ { false → y ; true → do y ← y ; return (x ∷ y)}) (return []) nms
    debugPrint "fndR" 9 (strErr ("FNames : " & show fnms) ∷ [])
    ffnms ← return $ foldr (λ x y → case (all? (λ z → isNo $ x == z) y) of λ { true → x ∷ y ; false → y}) [] fnms
    debugPrint "fndR" 9 (strErr ("FFNames : " & show ffnms) ∷ [])
    newNms ← return $ filter (λ x → all? (λ z → isNo $ x == z) pl) ffnms
    debugPrint "fndR" 9 (strErr ("New Names : " & show newNms) ∷ [])
    prevNms ← return $ pl ++ newNms
    debugPrint "fndR" 9 (strErr ("Previous Names : " & show prevNms) ∷ [])
    res ← foldr (λ x y → do (py , pnms) ← y ; nms ← findAllNamesRec py x ; return ((py ++ nms) , pnms ++ nms)) (return (prevNms , newNms)) newNms
    return $ snd res



checkHasNoInput : Name → TC ⊤
checkHasNoInput nm =
  do
    d ← getDefinition nm
    cls ← isFun? d
    case cls of
      λ { [] → typeError ((strErr "The function should not have absurd inputs.") ∷ []) ;
          [ clause ps t ] → case (length ps) of λ { zero → return unit ; (suc x) → typeError ((strErr "The main function should not have any input variables.") ∷ [])} ;
          [ absurd-clause ps ] → typeError ((strErr "Internal error. Please report this. 3") ∷ []) ; 
          (x ∷ t ∷ y) → typeError ((strErr "The main function should not have multiple clauses.") ∷ [])}


macro
  typeCheck : Name → Term → TC ⊤
  typeCheck nm hole =
    do
      caseM (checkPFType nm) of
        (λ { false → typeError {A = ⊤} ((strErr "Hey, this function does not return a PF record.") ∷ []) ;
             true → return unit})
      checkHasNoInput nm
      nms` ← findAllNamesRec [ nm ] nm
      nms ← return $ nm ∷ nms`
      debugPrint "tych" 9 (strErr ("typeCheck Names : " & show nms) ∷ [])
      mapM typeCheckS nms
      u ← quoteTC {A = ⊤} unit
      unify hole u


last : ∀{a} → {A : Set a} → List A → Maybe A
last [] = nothing
last [ x ] = just x
last (x ∷ zs@(x₁ ∷ xs)) = last zs


piLen : Term → TC Nat
piLen (pi a (abs s x)) =
  do
    n ← piLen x
    return $ suc n
piLen x = typeError ((strErr "Internal error, report it 4") ∷ [])

-- Agent Role
findARole : Term → TC $ Either Term Nat
findARole (pi a (abs s x)) = findARole x
findARole (def f args) = case (f == quote Protocol.PF) of
                           λ { (yes x) → case (last args) of
                                          λ { nothing → typeError ((strErr "Internal error, report it 5") ∷ []) ;
                                              (just t) → case t of
                                                           λ { (arg i (var x args)) → return $ right x ;
                                                               (arg i t) → return $ left t}} ;
                               (no x) → typeError ((strErr "Internal error, report it 6") ∷ [])}
findARole x = typeError ((strErr "Internal error, report it 7") ∷ [])






-- -- Case 1 It is a projection and not a local function.
-- performCheck4 : Term → List Clause → List Bool → TC ⊤
-- performCheck4 ty cls bprs =
--   do
--     pl ← piLen ty
--     {!!}


-- -- case 2 It is not a projection.

-- -- There are two more checks.
-- -- B : The type of PFs need to correspond to the resulting type. The roles must match. If the role is given through a var, all Pf functions in the definition must get that var as a first arg, we need to inspect its type.
-- -- If not, the type must have the same constant Role.
-- -- C : Those that get the Role as a var must give it to all other abstract PF arguments , because of that, we do not need to inspect vars for B.

