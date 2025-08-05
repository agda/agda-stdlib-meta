--------------------------------------------------------------------------------
-- ** Generic deriving of DecEq

-- Alternative to Tactic.Derive.DecEq that supports a different subset of types,
-- and typechecks faster in the presence of many fields/constructors.
--------------------------------------------------------------------------------
{-# OPTIONS -v DecEqFast:100 #-}
{-# OPTIONS --safe --with-K #-}
module Tactic.Derive.DecEqFast where

open import Meta.Prelude hiding ([_,_])

open import Relation.Nullary
open import Relation.Binary using () renaming (Decidable to Decidable²)
import Data.List as L
open L using ([]; _∷_; map)

open import Class.Show
open import Class.Semigroup
open import Class.Monoid
open import Class.Functor
open import Class.Bifunctor
open import Class.Monad
open import Class.DecEq.Core
open import Class.DecEq.Instances using (DecEq-Name)
open import Class.DecEq.WithK

open import Agda.Builtin.Reflection public
  using (modality; relevant; irrelevant)
open import Reflection.Syntax
open import Reflection.QuotedDefinitions
open import Reflection.Utils
open import Reflection.Utils.Debug
open Debug ("DecEqFast" , 100)
open import Reflection hiding (_>>=_; _>>_; _≟_)
open import Reflection.Utils.TCM

--
allPairs : List A → List (A × A)
allPairs xs = cartesianProduct xs xs

`λ∅∅ = `λ⦅ [ "()" , vArg? ] ⦆∅
--

-- ** patterns
module _ (toDrop : ℕ) {- module context -} where
  mkPattern : Name → TC
    ( Args Type           -- ^ type arguments of given constructor
    × ℕ                   -- ^ # of introduced variables
    × List (ℕ × Arg Type) -- ^ generated variables along with their type
    × Pattern             -- ^ generated pattern for given constructor
    )
  mkPattern c = do
    ty ← reduce =<< getType c
    let tys  = drop toDrop (argTys ty)
        n    = length tys
        vars = enumerate tys
    return
      $ tys
      , n
      , vars
      , Pattern.con c (map (λ{ (i , arg x _) → arg x (` i) }) vars)

module _ (toDrop : ℕ) {- module context -} where
  derive-DecEq′ : Definition → TC Term
  derive-DecEq′ (data-type _  []) = return `λ∅∅
  derive-DecEq′ (data-type ps cs) = do
    cls ← concatMap L.fromMaybe <$> mapM f (allPairs cs)
    return $ pat-lam cls []
    where
      go : ℕ → List (ℕ × Arg Type) → Term
      go _ []              = `yes (quote refl ◆)
      go n ((x , _) ∷ xs) =
        let i = n ∸ suc x in
        quote case_of_
          ∙⟦ quote _≟_ ∙⟦ ♯ (i + n) ∣ ♯ i ⟧
          ∣ `λ⟦ ``no (Pattern.var 0 {-"¬p"-})
                ⦅ [ "¬p" , vArg? ] ⦆⇒
                `no (`λ⟦ (quote refl ◇)
                          ⦅ [] ⦆⇒ (♯ 0 ⟦ quote refl ◆ ⟧)
                        ⟧)
              ∣ ``yes (quote refl ◇)
                ⦅ [] ⦆⇒ go n xs
              ⟧
          ⟧

      bumpFreeVars : (ℕ → ℕ) → List (ℕ × Arg Type) → List (ℕ × Arg Type)
      bumpFreeVars bump = go′ 0
        where
          go′ : ℕ → List (ℕ × Arg Type) → List (ℕ × Arg Type)
          go′ _ []            = []
          go′ x ((i , p) ∷ ps) = (bump i , fmap (mapFreeVars bump x) p) ∷ go′ (suc x) ps

      f : Name × Name → TC (Maybe Clause)
      f (c , c′) = do
        _ , n , pvs , pc  ← mkPattern toDrop c
        _ , n′ , pvs′ , pc′ ← mkPattern toDrop c′
        let
          tel = map (λ (i , argTy) → ("v" ◇ show i) , argTy) (pvs ++ bumpFreeVars (_+ n) pvs′)
          PC  = mapVariables (λ i → n + n′ ∸ suc i) pc
          PC′ = mapVariables (λ i → n′ ∸ suc i) pc′
        ty  ← reduce =<< getType c
        ty′ ← reduce =<< getType c′
        b   ← compatible? (resultTy ty) (resultTy ty′)
        return $
          if b then just (⟦ PC ∣ PC′ ⦅ tel ⦆⇒ if c == c′ then go n (filter (isVisible? ∘ proj₂) pvs)
                                                        else `no `λ∅∅ ⟧)
              else nothing

  derive-DecEq′ (record-type rn fs) = do
    return $ `λ⟦ "r" ∣ "r′" ⇒ go fs ⟧
    where
      go : List (Arg Name) → Term
      go [] = `yes (quote refl ◆)
      go (arg (arg-info _ (modality relevant _)) n ∷ args) =
        quote case_of_
          ∙⟦ quote _≟_ ∙⟦ n ∙⟦ ♯ 1 ⟧ ∣ n ∙⟦ ♯ 0 ⟧ ⟧
          ∣ `λ⟦ ``no (Pattern.var 0 {-"¬p"-})
              ⦅ [ "¬p" , vArg? ] ⦆⇒
                  `no (`λ⟦ (quote refl ◇)
                          ⦅ [] ⦆⇒ (♯ 0 ⟦ quote refl ◆ ⟧)
                          ⟧)
              ∣ ``yes (quote refl ◇)
              ⦅ [] ⦆⇒ go args
              ⟧
          ⟧
      go (arg (arg-info _ _) _ ∷ args) = go args
  derive-DecEq′ _ = error "[not supported] not a data type or record"

derive-DecEq : List (Name × Name) → TC ⊤
derive-DecEq xs = do
    (record-type c _) ← getDefinition (quote DecEq)
      where _ → error "impossible"

    ys ← forM xs λ (n , f) → do
      f′ ← freshName (show {A = Name} f)
      T ← getType n
      ctx ← getContext
      d ← getDefinition n

      let tel = argTys T -- tyTele T
          n′ = apply⋯ tel n
          is = argTys T
      let mctx = take (parameters d ∸ length ctx) is
          mtel = map ("_" ,_) mctx
          pc = map (λ where (i , _) → hArg (` i) ) (enumerate mctx)

      -- fᵢ′ : ∀ ⋯ → Decidable² {A = Tᵢ ⋯} _≡_
      let ty′ = ∀indices⋯ tel
              $ def (quote Decidable²) (hArg? ∷ hArg n′ ∷ vArg (quote _≡_ ∙) ∷ [])
      declareDef (vArg f′) ty′

      -- instance fᵢ : ∀ ⋯ → DecEq (Tᵢ ⋯)
      let ty = ∀indices⋯ tel
             $ quote DecEq ∙⟦ n′ ⟧
      declareDef (iArg f) ty
      -- fᵢ ⋯ = λ where ._≟_ → fᵢ′
      defineFun f [ clause mtel pc (c ◆⟦ f′ ∙ ⟧) ]

      -- fᵢ′ ⋯ = λ where
      --    (c₀ x y) (c₀ x′ y′) → case x ≟ x′ of ⋯
      --    ⋯
      t ← inContext (L.reverse mtel) $ do
        ctx ← getContext
        derive-DecEq′ (length mtel) d

      return (f′ , (pc , mtel) , t)

    return⊤ $ forM ys λ (f′ , (pc , mtel) , t) →
      defineFun f′ [ clause mtel pc t ]

--------------------------
-- Examples

private

-- ** record types

  open import Tactic.Defaults
  open import Data.Integer using (ℤ)
  open import Data.Fin using (Fin)

  record R⁰ : Set where
  unquoteDecl r⁰ = derive-DecEq [ quote R⁰ , r⁰ ]

  record R¹ : Set where
    field
      x : ℕ
  unquoteDecl r¹ = derive-DecEq [ quote R¹ , r¹ ]

  record R² : Set where
    field
      x : ℕ × ℤ
      y : ⊤ ⊎ Bool
  unquoteDecl r² = derive-DecEq [ quote R² , r² ]

-- ** inductive datatypes

  data X⁰ : Set where
  unquoteDecl x⁰ = derive-DecEq [ quote X⁰ , x⁰ ]

  data X¹ : Set where
    x : X¹
  unquoteDecl x¹ = derive-DecEq [ quote X¹ , x¹ ]

  data X² : Set where
    x y : X²
  unquoteDecl x² = derive-DecEq [ quote X² , x² ]

  data XX : Set where
    c₂ : List X² → XX
    c₁ : X¹ → X² → XX
  unquoteDecl xx = derive-DecEq [ quote XX , xx ]

  data XXX : Set where
    c₂′  : List X² → XXX
    _⊗⊗_ : XXX → XXX → XXX
  unquoteDecl xxx = derive-DecEq [ quote XXX , xxx ]

-- ** recursive datatypes

  data ℕ′ : Set where
    O : ℕ′
    S : ℕ′ → ℕ′
  unquoteDecl DecEq-ℕ′ = derive-DecEq [ quote ℕ′ , DecEq-ℕ′ ]

-- ** list recursion

  data Nats : Set where
    O : Nats
    S : List Nats → Nats

  -- {-# TERMINATING #-}
{- *** T0D0: figure out how to pass termination checker

  go : Decidable² {A = Nat} _≡_
  instance
    dn : DecEq Nat
    dn ._≟_ = go
  go = λ
    { O O → yes refl
    ; O (S x0) → no (λ { () })
    ; (S x0) O → no (λ { () })
    ; (S x0) (S x0′)
        → case _≟_ ⦃ DecEq-List ⦃ dn ⦄ ⦄ x0 x0′ of λ
            { (no ¬p) → no λ { refl → ¬p refl }
            ; (yes refl) → yes refl  ⦄
-}
  -- unquoteDecl DecEq-Nats = derive-DecEq [ quote Nats , DecEq-Nats ]

-- ** mutually recursive datatypes

  data M₁ : Set
  data M₂ : Set
  data M₁ where
    m₁ : M₁
    m₂→₁ : M₂ → M₁
  data M₂ where
    m₂ : M₂
    m₁→₂ : M₁ → M₂
  unquoteDecl DecEq-M₁ DecEq-M₂ = derive-DecEq $ (quote M₁ , DecEq-M₁) ∷ (quote M₂ , DecEq-M₂) ∷ []

-- ** make sure all derivations were successful
  open import Data.List.Relation.Unary.All using (All; []; _∷_)
  _ : All (λ x → Decidable² {A = x} _≡_) (R⁰ ∷ R¹ ∷ R² ∷ X⁰ ∷ X¹ ∷ X² ∷ XX ∷ ℕ′ ∷ M₁ ∷ M₂ ∷ [])
  _ = _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ _≟_ ∷ []

-- ** indexed types

  data Fin′ : ℕ → Set where
    O : ∀ {n} → Fin′ (suc n)
    S : ∀ {n} → Fin′ n → Fin′ (suc n)
  unquoteDecl DecEq-Fin′ = derive-DecEq [ quote Fin′ , DecEq-Fin′ ]
  _ : ∀ {n} → Decidable² {A = Fin′ n} _≡_
  _ = _≟_

  data λExprℕ (n : ℕ) : Set where
    ƛ_ : Fin n → λExprℕ n
  unquoteDecl DecEq-λExprℕ = derive-DecEq [ quote λExprℕ , DecEq-λExprℕ ]

  data Boolℕ : Bool → ℕ → Set where
    O : Boolℕ true 0
  unquoteDecl DecEq-Boolℕ = derive-DecEq [ quote Boolℕ , DecEq-Boolℕ ]
  _ : ∀ {b n} → Decidable² {A = Boolℕ b n} _≡_
  _ = _≟_

  data Boolℕ² : Bool → ℕ → Set where
    O : Boolℕ² false 0
    I : Boolℕ² true  1
  unquoteDecl DecEq-Boolℕ² = derive-DecEq [ quote Boolℕ² , DecEq-Boolℕ² ]
  _ : ∀ {b n} → Decidable² {A = Boolℕ² b n} _≡_
  _ = _≟_

  data Wrapℕ : Set where
    Mk : ℕ → Wrapℕ
  unquoteDecl DecEq-Wrapℕ = derive-DecEq [ quote Wrapℕ , DecEq-Wrapℕ ]

  variable
    n : ℕ
    wn : Wrapℕ

  data Exprℕ : Wrapℕ → Set where
    var : Fin n → Exprℕ (Mk n)
    ‵ : ∀ {x} → ℕ → Exprℕ x
  unquoteDecl DecEq-Exprℕ = derive-DecEq [ quote Exprℕ , DecEq-Exprℕ ]

  data Enum : Set where
    I II : Enum
  unquoteDecl DecEq-Enum = derive-DecEq [ quote Enum , DecEq-Enum ]

  variable en : Enum

  Time = ℕ

  data Exprℕ′ : Wrapℕ → Enum → Set where
    var : Fin n → Exprℕ′ (Mk n) I
    ‵ : ℕ → Exprℕ′ wn II
    _`+_ : Exprℕ′ wn II → Exprℕ′ wn II → Exprℕ′ wn II
    _`-_ : Exprℕ′ wn II → Exprℕ′ wn II → Exprℕ′ wn II
    _`=_ : Exprℕ′ wn II → Exprℕ′ wn II → Exprℕ′ wn I
    _`<_ : Exprℕ′ wn II → Exprℕ′ wn II → Exprℕ′ wn I

    `if_then_else_ : Exprℕ′ wn I → Exprℕ′ wn en → Exprℕ′ wn en → Exprℕ′ wn en

    -- Size
    ∣_∣ : Exprℕ′ wn II → Exprℕ′ wn II

    -- Hashing
    hash : Exprℕ′ wn II → Exprℕ′ wn II

    -- Signature verification
    versig : List ℕ → List (Fin n) → Exprℕ′ (Mk n) I

    -- Temporal constraints
    absAfter_⇒_ : Time → Exprℕ′ wn en → Exprℕ′ wn en
    relAfter_⇒_ : Time → Exprℕ′ wn en → Exprℕ′ wn en

  unquoteDecl DecEq-Exprℕ′ = derive-DecEq [ quote Exprℕ′ , DecEq-Exprℕ′ ]

-- ** parametrized datatypes
{-
  data Expr (A : Set) : Set where
    Con : A → Expr A
    _⊕_ : Expr A → Expr A → Expr A
  unquoteDecl DecEq-Expr  = derive-DecEq [ quote Expr , DecEq-Expr ]
  _ : ∀ {A} ⦃ _ : DecEq A ⦄ → Decidable² {A = Expr A} _≡_
  _ = _≟_

  data Exprℤ : ℤ → Set where
    Con : ∀ {n} → ℤ → Exprℤ n
    _⊕_ : ∀ {x y z} → Exprℤ x → Exprℤ y → Exprℤ z
  unquoteDecl DecEq-Exprℤ  = derive-DecEq [ quote Exprℤ , DecEq-Exprℤ ]
  _ : ∀ {n} → Decidable² {A = Exprℤ n} _≡_
  _ = _≟_
-}

-- ** indexed records

  record Pos (n : ℕ) : Set where
    field
      pos : Fin n
  unquoteDecl DecEq-Pos  = derive-DecEq [ quote Pos , DecEq-Pos ]
  _ : ∀ {n} → Decidable² {A = Pos n} _≡_
  _ = _≟_

-- ** datatypes inside module

  module Test₁ (A : Set) ⦃ _ : DecEq A ⦄ (B : Set) ⦃ _ : DecEq B ⦄ where

    data X : ℕ → Set where
      x₀ y₀ z₀ : X 0
      x₁ y₁ z₁ : X 1
      fromA    : ∀ {n} → A → X n
      fromB    : ∀ {n} → B → X n
    unquoteDecl DecEq-Test1X = derive-DecEq [ quote X , DecEq-Test1X ]

    _ : ∀ {n} → Decidable² {A = X n} _≡_
    _ = _≟_

    record R : Set where
      field
        r₁ : A
        r₂ : B
    unquoteDecl DecEq-Test1R = derive-DecEq [ quote R , DecEq-Test1R ]
    _ : Decidable² {A = R} _≡_
    _ = _≟_

    record R′ : Set where
      field
        r₁ : A × B
        r₂ : X 0
    unquoteDecl DecEq-Test1R′ = derive-DecEq [ quote R′ , DecEq-Test1R′ ]
    _ : Decidable² {A = R′} _≡_
    _ = _≟_

  module _ (A : Set) ⦃ _ : DecEq A ⦄ {B : Set} ⦃ _ : DecEq B ⦄ where
    open Test₁ A B

    _ : ∀ {n} → Decidable² {A = X n} _≡_
    _ = _≟_
    _ : Decidable² {A = R} _≡_
    _ = _≟_
    _ : Decidable² {A = R′} _≡_
    _ = _≟_

  unquoteDecl DecEq-Test1R = derive-DecEq [ quote Test₁.R , DecEq-Test1R ]
  _ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {B : Set} ⦃ _ : DecEq B ⦄
    → Decidable² {A = Test₁.R A B} _≡_
  _ = _≟_

  -- unquoteDecl DecEq-Test1R′ = derive-DecEq [ quote Test₁.R′ , DecEq-Test1R′ ]
  -- _ : ∀ {A : Set} ⦃ _ : DecEq A ⦄ {B : Set} ⦃ _ : DecEq B ⦄
  --   → Decidable² {A = Test₁.R′ A B} _≡_
  -- _ = _≟_

  data λExprℕ′ (mn : Wrapℕ) : Set where
    ƛ_ : Exprℕ′ mn II → λExprℕ′ mn
  unquoteDecl DecEq-λExprℕ′ = derive-DecEq [ quote λExprℕ′ , DecEq-λExprℕ′ ]


  module Test₂ (A : Set) ⦃ _ : DecEq A ⦄ where
    data Label : Set where
      auth-divide : A → ℕ → ℕ → ℕ → Label
    unquoteDecl DecEq-Label = derive-DecEq [ quote Label , DecEq-Label ]

  data Letter : Set where
    α ἄ ὰ ά Ἀ έ ἔ ῆ ἣ η ι ϊ ί ῖ ο ὐ υ ω γ δ θ κ ƛ μ ν Π ρ ς χ : Letter
  unquoteDecl DecEq-Letter = derive-DecEq [ (quote Letter , DecEq-Letter) ]

  -- open import Tactic.Derive.TestTypes
