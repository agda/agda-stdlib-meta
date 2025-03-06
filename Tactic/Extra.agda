{-# OPTIONS --safe --without-K #-}
-- {-# OPTIONS -v tactic.extra:100 #-}
module Tactic.Extra where

open import Meta.Prelude

open import Data.Integer as Int using (ℤ)
open import Data.List using (List; drop; map; [_]; [])
open import Data.Nat as Nat using (ℕ)
open import Data.Vec using (Vec; []; _∷_)

open import Reflection hiding (_>>=_; _>>_; _≟_)
open import Reflection.Syntax
open import Reflection.Tactic
open import Reflection.Utils
open import Reflection.Utils.Debug
open import Reflection.Utils.TCI

open import Class.DecEq
open import Class.Functor
open import Class.Monad
open import Class.Semigroup
open import Class.Show

open Debug ("tactic.extra" , 100)

macro
  ∶t : Name → Hole → TC ⊤
  ∶t n hole = unify hole =<< getType n

private
  _ = (∶t Nat._+_) ≡ (ℕ → ℕ → ℕ)
    ∋ refl
  _ = (∶t Int._+_) ≡ (ℤ → ℤ → ℤ)
    ∋ refl

  id′ : ∶t id
  id′ = λ x → x

∶type : Name → TC Type
∶type = getType

∶set : Term → Tactic
(∶set t) hole = unify hole t

-- :t : Name → TC X
-- :s : X → Tactic
--        ~ Hole → TC ⊤
-- macro
--   ∶t : Name → Tactic
--   (∶t n) hole = (∶type n >>= ∶set hole

∶def : Name → TC Definition
∶def = getDefinition

macro give_ : ∀ {ℓ} {A : Set ℓ} → A → Hole → TC ⊤
      give_ {A = A} t hole = unify hole =<< quoteTC (A ∋ t)
private _ = 5 ≡ 5 ∋ give refl

-- ** Builders (of function definitions).
FunDef = Type × Clauses

getFunDef : Name → TC FunDef
getFunDef n = do
  ty ← getType n
  function cs ← getDefinition n
    where _ → error "[getFunDef] not a function"
  return (ty , cs)

Builder : ∀ {ℓ} → Set ℓ → Set ℓ
Builder A = Name → A
Builder⊤ = Builder (TC ⊤)

build : FunDef → Builder⊤
   -- ~ FunDef → ∗Name∗ → TC ⊤
build (ty , cs) f = do
  declareDef (vArg f) ty
  defineFun f         cs

-- Builder′ As = As ⇉ (Name → TC ⊤)
-- Tactic′  As = As ⇉ (Hole → TC ⊤)

private
  default : Builder (Name → TC ⊤)
      -- ~ ∗Name∗ → Name → TC ⊤
  default f n = do
    d@(ty , cs) ← getFunDef n
    print $ "[default] retrieving default implementation for " ◇ show n
          ◇ "\n\t" ◇ show n ◇ " : " ◇ show ty
          ◇ "\n\t" ◇ show n ◇ " = " ◇ show cs
    build d f

  default2 : ℕ → Builder (Name → TC ⊤)
        -- ~ ℕ → ∗Name∗ → Name → TC ⊤
  default2 _ = default

  default3 : ℕ → Builder (ℕ → Name → TC ⊤)
        -- ~ ℕ → ∗Name∗ → ℕ → Name → TC ⊤
  default3 _ f x n = default2 x f n

  default4 : ℕ → Builder (ℕ → Name → ℕ → TC ⊤)
        -- ~ ℕ → ∗Name∗ → ℕ → Name → ℕ → TC ⊤
        -- ~ ℕ → ∗Name∗ → ℕ → Builder (ℕ → TC ⊤)
  default4 _ f x n y = default3 x f y n

  default5 : ℕ → ℕ → Builder (ℕ → Name → ℕ → TC ⊤)
  default5 _ z f x n y = default4 x f y n z

  default6 : ℕ → ℕ → Builder (ℕ → Name → ℕ → ℕ → TC ⊤)
  default6 _ z f x n y _ = default4 x f y n z

  default7 : ℕ → ℕ → Builder (ℕ → Name → ℕ → Name → ℕ → TC ⊤)
  default7 _ z f x n y s _ =
    if s == n then default4 x f y n z
              else default4 x f y s z

-- ** Converting meta-programs that return `Term` to macros.

open import Function.Nary.NonDependent using (Sets; _⇉_; mapₙ)
∶_ : ∀ {n ls} {As : Sets n ls} → As ⇉ TC Term → As ⇉ Tactic
∶_ {n = n} = mapₙ n go
  where
    go : TC Term → Tactic
    go k hole = unify hole =<< k

macro
  ∶¹_ : ∀ {A : Set} → (A → TC Term) → (A → Tactic)
  ∶¹_ {A} = ∶_ {As = A , lift tt}

  ∶²_ : ∀ {A B : Set} → (A → B → TC Term) → (A → B → Tactic)
  ∶²_ {A}{B} = ∶_ {As = A , B , lift tt}

  ∶³_ : ∀ {A B C : Set} → (A → B → C → TC Term) → (A → B → C → Tactic)
  ∶³_ {A}{B}{C} = ∶_ {As = A , B , C , lift tt}

-- ** Providing names without quoting.
macro
  _↜_ : ∀ {ℓ} {X : Set ℓ} → Builder X → Name → Tactic
    -- ~ (Name → TC ⊤) → Name → Hole → TC ⊤
  (builder ↜ f) hole = quoteTC (builder f) >>= unify hole

private
  record R : Set where
    field x : ℕ
    y = x

  module MR where
    x = 5
    -- y = x
    -- unquoteDecl y = default y (quote R.y)
    -- unquoteDecl y = default y ⟨ R.y ⟩
    -- unquoteDecl y = default y ⟨ R.y ⟩
    -- unquoteDecl y = default2 0 y ⟨ R.y ⟩
    -- unquoteDecl y = default3 0 y 1 ⟨ R.y ⟩
    -- unquoteDecl y = (∶ default3 0 y) 1 (quote R.y)
    -- unquoteDecl y = (default4 0 y 1 ⟨ R.y ⟩) 2
    -- unquoteDecl y = ⟨ default4 0 y 1 ─ R.y ⟩ 2
    -- unquoteDecl y = (default5 0 1 y 2 ⟨ R.y ⟩) 3
    -- unquoteDecl y = (default5 0 1 y 2 -∙- R.y) 3
    -- unquoteDecl y = (default6 0 1 y 2 ⟨ R.y ⟩) 3 4
    -- unquoteDecl y ((default7 0 1 y 2 ⟨ R.y ⟩) 3 ⟨ R.y ⟩) 4
    unquoteDecl y = ((default7 0 1 y 2 ↜ R.y) 3 ↜ R.y) 4

  _ = x where open R record {MR}

-- ** Testing single-level pattern match that eliminates into ⊤.

getPatTele : Name → TC PatTelescope
getPatTele cn = do
  print $ "Getting pattern telescope for constructor: " ◇ show cn
  ty ← getType cn
  print $ "  ty: " ◇ show ty
  data-cons n _ ← getDefinition cn
    where _ → _IMPOSSIBLE_
  print $ "  n: " ◇ show n
  data-type ps _ ← getDefinition n
    where _ → _IMPOSSIBLE_
  print $ "  ps: " ◇ show ps
  let tys = drop ps (argTys ty)
  print $ "  argTys: " ◇ show tys
  let tel = map ("_" ,_) (fmap (const unknown) <$> tys)
  print $ "  tel: " ◇ show tel
  return tel

mkCase : Name → Type → (PatTelescope → TC Term) → TC Term
mkCase n n→ty mkT = do
  data-type ps cs ← getDefinition n
    where _ → error $ "[mkCase] not a datatype"
  vΠ[ _ ∶ n ∙ ] ty ← return n→ty
    where _ → error $ "[mkCase] not a valid goal"
  cls ← mapM mkC cs
  return $ quote _∋_ ∙⟦ vΠ[ "_" ∶ n ∙ ] ty ∣ pat-lam cls [] ⟧
  where
    mkP : ℕ × Abs (Arg Type) → Abs $ Arg $ Type × Pattern
    mkP (i , x) = fmap (fmap $ _, ` i) x

    mkC : Name → TC Clause
    mkC cn = do
      tel ← getPatTele cn
      let
        tys : Args Type
        tys = map proj₂ tel

        itys = enumerate tys

        cArgsᵖ : Args Pattern
        cArgsᵖ = map (λ (i , at) → fmap (const $ var i) at) itys
      print $ "cArgs: " ◇ show cArgsᵖ
      t ← mkT tel
      print $ "t: " ◇ show t
      return $ clause tel [ vArg $ con cn cArgsᵖ ] t
macro run-mkCase = ∶_ {As = Name , Term , (PatTelescope → TC Term) , lift tt} mkCase

genTestMatch : Name → Name → TC ⊤
genTestMatch f n = do
  print "****************************************"
  print $ "Generating match for " ◇ show n
  let ty = vΠ[ "_" ∶ n ∙ ] (quote ⊤ ∙)
  print $ "\t " ◇ show f ◇ " : " ◇ show ty
  declareDef (vArg f) ty
  t ← mkCase n ty (const $ return $ quote tt ◆)
  print $ "\t " ◇ show f ◇ " = " ◇ show t
  defineFun f [ ⟦⇒ t ⟧ ]

private
  variable n : ℕ
  data Xˡ : Set → Set₁ where
    [1] : Xˡ String
    [2] : Xˡ A → Xˡ (Vec A n)
  data Xʳ : Set → Set₁ where
    [3] : Xʳ ℕ
    [4] : Xʳ A → Xʳ (List A)
  data X : Set₁ where
    [L]_ : Xˡ A → X
    [R]_ : Xʳ A → X

  _ = run-mkCase X (X → ⊤) λ _ → return (quote tt ◆)

  unquoteDecl testX = genTestMatch testX (quote X)
  testX-manual : X → ⊤
  testX-manual = λ where
    ([L] _) → tt
    ([R] _) → tt
  _ = testX ≡ testX-manual ∋ refl

  -- T0D0: dependent types
  -- postulate
  --   P Q : Set
  --   x ∅ˣ : P
  --   ∅ʸ y : Q

  -- data _~_ : P → Q → Set where
  --   [L] : x ~ ∅ʸ
  --   [R] : ∅ˣ ~ y

  -- unquoteDecl test~ = genTestMatch test~ (quote _~_)
