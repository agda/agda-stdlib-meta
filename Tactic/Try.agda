{-# OPTIONS --with-K #-}
-- {-# OPTIONS -v tactic.try:100 #-}
module Tactic.Try where

open import Meta.Prelude

open import Data.List

open import Reflection hiding (_>>=_; _>>_; _≟_)
open import Reflection.Syntax
open import Reflection.Utils
open import Reflection.Utils.Debug
open import Reflection.Utils.TCM
open import Relation.Nullary

open import Class.DecEq
open import Class.Functor
open import Class.Monad
open import Class.Semigroup
open import Class.Show

open Debug ("tactic.try" , 100)

_∙_ : Term → Args Term → TC Term
t ∙ [] = return t
t ∙ es′@(_ ∷ _) with t
... | var     x  es = return $ var     x  (es′ ++ es)
... | con     c  es = return $ con     c  (es′ ++ es)
... | def     f  es = return $ def     f  (es′ ++ es)
... | pat-lam cs es = return $ pat-lam cs (es′ ++ es)
... | meta    x  es = return $ meta    x  (es′ ++ es)
... | e             = error $ "cannot apply arguments to " ◇ show t

private module _ {ℓ ℓ′} {A : Set ℓ} {B : Set ℓ′} ⦃ _ : DecEq A ⦄ where

  import Data.List.Membership.DecPropositional {A = A} _≟_ as DL

  -- NB: right-biased, e.g. nubBy ∣_∣ [-1,0,1] = [0,1]
  nubBy : (B → A) → List B → List B
  nubBy f [] = []
  nubBy f (x ∷ xs) with f x DL.∈? map f xs
  ... | yes _ = nubBy f xs
  ... | no  _ = x ∷ nubBy f xs

nodup : List Term → List Term
nodup = nubBy show

private
  doN : {{_ : DecEq A}} → ℕ → (A → TC A) → (A → TC A)
  doN 0       _ x = return x
  doN (suc n) f x = do
    y ← f x
    if (y ≠ x) then doN n f y else return x

  ifM_then_else_ : TC Bool → TC A → TC A → TC A
  ifM mb then k else k′ = do
    b ← mb
    if b then k else k′

  caseM_of_ : TC A → (A → TC B) → TC B
  caseM k of f = do
    x ← k
    case x of f

  infixl 0 _∣_
  _∣_ : TC A → TC A → TC A
  f ∣ g = catchTC f g

  amb : List (TC A) → TC A
  amb = foldr _∣_ (error "∅")

  infix 4 _≔_
  _≔_ : Term → List Term → TC ⊤
  t ≔ es = amb $ map (unify t) es

  purely : TC A → TC A
  purely k = runSpeculative (fmap (_, false) k)

record Subterms (A : Set) : Set where
  field
    subterms : A → List Term

open Subterms {{...}}

instance
  STerm : Subterms Term
  STerm .subterms t = t ∷ (case t of λ where
    (var _ []) → []
    (var x (arg _ e ∷ as)) → subterms e ++ subterms (var x as)
    (con _ []) → []
    (con c (arg _ e ∷ as)) → subterms e ++ subterms (con c as)

    (def _ []) → []
    (def f (arg _ e ∷ as)) → subterms e ++ subterms (def f as)
    (pi (arg _ ty) (abs _ e)) → subterms ty ++ subterms e
    _ → [])

  SArg : {{_ : Subterms A}} → Subterms (Arg A)
  SArg .subterms = subterms ∘ unArg

  SAbs : {{_ : Subterms A}} → Subterms (Abs A)
  SAbs .subterms = subterms ∘ unAbs

  SList : {{_ : Subterms A}} → Subterms (List A)
  SList .subterms = concatMap subterms

fits? : Type → Term → TC Bool
fits? ty e = inferType e >>= compatible? ty

apply? : Type → Type → TC (Maybe (Args Type))
apply? ty ty₀ = go ty []
  where
    go : Type → Args Type → TC (Maybe (Args Type))
    go ty as =
      ifM compatible? ty ty₀ then
        return (just as)
      else (case ty of λ where
        (Π[ _ ∶ a ] ty′) → go ty′ (as ++ [ a ])
        _                → return nothing)

{-# TERMINATING #-}
allCandidates : List Term → Type → TC (List Term)
tryOut : List Term → Term × Type → TC (List Term)

allCandidates db ty = fmap concat $ mapM go db
  where
    go : Term → TC (List Term)
    go e = do
      eTy ← inferType e
      caseM apply? eTy ty of λ where
        nothing    → return []
        (just tys) → tryOut db (e , eTy)

tryOut db (f , fTy) = purely (do
  cs ← forM (argTys fTy) λ where
    (arg i ty) → do
      cs′ ← allCandidates db ty
      return $ map (arg i) cs′
  mapM (f ∙_) (combinations cs)) ∣ return db
  where
    -- e.g. combinations [[1,2,3],[4,5]] ≡ [[1,4],[1,5],[2,4],[2,5],[3,4],[3,5]]
    combinations : List (List A) → List (List A)
    combinations []         = [ [] ]
    combinations (xs ∷ xss) = concatMap (λ x → map (x ∷_) xss′) xs
      where xss′ = combinations xss

-- applyCandidates : List Term → Term → TC (List Term)
-- applyCandidates candidates f = purely (do
--   fTy ← inferType f
--   cs ← forM (argTys fTy) λ where
--     (arg i ty) → fmap (map (arg i)) $ filterM (fits? ty) candidates
--   mapM (f ∙_) (combinations cs)) ∣ return candidates

-- expand : List Term → TC (List Term)
-- expand cs = do
--   cs′ ← fmap concat $ forM cs (applyCandidates cs)
--   return $ nodup $ cs ++ cs′

prints : {{_ : Show A}} → String → List A → TC ⊤
prints pre xs = print (pre ◇ " {") >> go xs
  where
    go : {{_ : Show A}} → List A → TC ⊤
    go [] = print "}"
    go (x ∷ xs) = print ("\t" ◇ show x) >> go xs

mapArgs : (Args Term → Args Term) → Term → Term
mapArgs f t₀ with t₀
... | var x as = var x (f as)
... | con x as = con x (f as)
... | def x as = def x (f as)
... | lam x (abs s t) = lam x (abs s $ mapArgs f t)
... | _ = t₀

countLambdas : Term → ℕ
countLambdas (lam _ (abs _ t)) = suc $ countLambdas t
countLambdas _ = 0

η-reduce : Term → Term
-- η-reduce t₀@(lam v₀ (abs _ t)) = mapArgs go t
--   where
--     λ♯ = countLambdas t

--     go : Args Term → Args Term
--     go as with L.initLast as
--     ... | [] = as
--     ... | as′ L.∷ʳ' arg (arg-info v _) t′ = if (v == v₀) ∧ (t′ == var λ♯ []) then as′ else as
η-reduce t = t

viewTerm : Term → TC (Term × Type)
viewTerm t = do
  -- ty ← inferType t
  -- print $ show t ◇ " : " ◇ show ty
  -- let t′ = η-reduce t
  -- ty′ ← inferType t′
  -- print "  ——→"
  -- print $ show t′ ◇ " : " ◇ show ty′
  -- return (t′ , ty′)
  fmap (t ,_) (inferType t)

tryWith : List Term → Term → Term → TC ⊤
tryWith userDB f₀ hole₀ = do
  print "---------------------------------"
  (hole , holeTy) ← viewTerm hole₀
  print $ "hole : " ◇ show holeTy
  (f , fTy) ← viewTerm f₀
  print $ show f ◇ " : " ◇ show fTy
  ctx ← getContext
  printCurrentContext
  let
    db : List Term
    db = nodup
       $ map ♯ (upTo $ length ctx)
      ++ subterms holeTy
      ++ subterms (map proj₂ ctx)
      ++ userDB
      ++ [ unknown ]
  prints "db" db
{-
  db′ ← doN 2 expand db
  print $ "db′: " ◇ show db′

  es ← applyCandidates db′ f
-}
  es ← tryOut db (f , fTy)
  prints "es" es

  hole ≔ es

macro
  try_∶-_ : Term → List Term → Term → TC ⊤
  try t ∶- userDB = tryWith userDB t

  try : Term → Term → TC ⊤
  try = tryWith []

private
  test₀ : (Bool → ℕ) → Bool → ℕ
  test₀ f b = try f

  _ : test₀ (if_then 1 else 0) true ≡ 1
  _ = refl

  test : (Bool → ℕ) → ℕ
  test f = try f ∶- ( quote true ◆
                    ∷ quote Bool ∙
                    ∷ quote ℕ ∙
                    ∷ quoteTerm (1 + 1)
                    ∷ [])

  _ : test (if_then 1 else 0) ≡ 1
  _ = refl

  test′ : ⊤ → (Bool → ℕ) → (⊤ → Bool) → ℕ
  test′ t f g = try f

  _ : test′ tt (if_then 1 else 9) (λ tt → true) ≡ 1
  _ = refl

  test₂ : (ℕ → Bool) → ℕ → ℕ → Bool
  test₂ f n m = try f

  _ : test₂ (_== 42) 10 42 ≡ true
  _ = refl
