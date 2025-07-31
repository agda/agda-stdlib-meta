-- Deriving decidable equality. This works in several cases that use
-- mutual recursion, examples are at the bottom.
--
-- TODO: This breaks with:
-- - dependent records, e.g. Product
-- - anything listed in Tactic.Derive
-- - maybe more

{-# OPTIONS -v allTactics:100 #-}
{-# OPTIONS --safe --with-K #-}
module Tactic.Derive.DecEq where

open import Meta.Prelude
open import Meta.Init

import Data.List as L
import Data.List.NonEmpty as NE

open import Relation.Nullary

open import Reflection.Tactic
open import Reflection.QuotedDefinitions
open import Reflection.AST.DeBruijn
open import Reflection.AST.Pattern using () renaming (_≟_ to _≟-Pattern_)

open import Class.DecEq.Core
open import Class.Functor
open import Class.MonadTC.Instances
open import Class.Traversable

open import Tactic.ClauseBuilder
open import Tactic.Derive (quote DecEq) (quote _≟_)


open ClauseExprM

-- simply typed annotated case_of_, giving better performance than without a type annotation
-- the type annotation prevents elaboration time from doubling on every argument to a constructor
`case_returning_of_ : Term → Term → Term → Term
`case t returning t' of t'' = def (quote case_of_) (hArg? ∷ hArg? ∷ hArg? ∷ hArg t' ∷ vArg t ∷ vArg t'' ∷ [])

private
  instance _ = ContextMonad-MonadTC

  -- Here's an example of what code this generates, here for a record R with 3 fields:
  -- DecEq : DecEq R
  -- DecEq ._≟_ ⟪ x₁ , x₂ , x₃ ⟫ ⟪ y₁ , y₂ , y₃ ⟫ =
  --   case (x₁ ≟ y₁) of λ where
  --     (false because ¬p) → no (case ¬p of λ where (ofⁿ ¬p) refl → ¬p refl)
  --     (true because p₁) → case (x₂ ≟ y₂) of λ where
  --       (false because ¬p) → no (case ¬p of λ where (ofⁿ ¬p) refl → ¬p refl)
  --       (true because p₂) → case (x₃ ≟ y₃) of λ where
  --         (false because ¬p) → no (case ¬p of λ where (ofⁿ ¬p) refl → ¬p refl)
  --         (true because p₃) →  yes (case p₁ , p₂ , p₃ of λ where (ofʸ refl , ofʸ refl , ofʸ refl) → refl)

  -- patterns almost like `yes` and `no`, except that they don't match the `Reflects` proof
  -- delaying maching on the `Reflects` proof as late as possible results in a major speed increase
  pattern ``yes' x = quote _because_ ◇⟦ quote true  ◇ ∣ x ⟧
  pattern ``no'  x = quote _because_ ◇⟦ quote false ◇ ∣ x ⟧

  module _ (transName : Name → Maybe Name) where

    eqFromTerm : Term → Term → Term → Term
    eqFromTerm (def n _) t t' with transName n
    ... | just n'     = def (quote _≟_) (iArg (n' ∙) ∷ vArg t ∷ vArg t' ∷ [])
    ... | nothing     = quote _≟_ ∙⟦ t ∣ t' ⟧
    eqFromTerm _ t t' = quote _≟_ ∙⟦ t ∣ t' ⟧

    -- `nothing`: outside of the diagonal, not equal
    -- `just`: on the diagonal, with that pattern, could be equal
    -- assume that the types in the pattern are properly normalized
    genBranch : Maybe SinglePattern → TC Term
    genBranch nothing         = return $ `no `λ⦅ [ ("" , vArg?) ] ⦆∅
    genBranch (just ([] , _)) = return $ `yes `refl
    genBranch (just p@(l@(x ∷ xs) , arg _ pat)) = do
      (con n args) ← return pat
        where _ → error1 "BUG: genBranch"
      typeList ← traverse inferType (applyUpTo ♯ (length l))
      let info = L.zip typeList (downFrom (length l))
      let ty = quote Dec ∙⟦ con n (applyDownFrom (vArg ∘ ♯ ∘ (_+ length l)) (length l))
                         `≡ con n (applyDownFrom (vArg ∘ ♯) (length l)) ⟧
      return $ foldl (λ t (eq , k) → genCase (weaken k ty) (eqFromTerm eq) t) genTrueCase info
      where
        k = ℕ.suc (length xs)

        vars : NE.List⁺ ℕ
        vars = 0 NE.∷ applyUpTo ℕ.suc (length xs)

        -- case (xᵢ ≟ yᵢ) of λ { (false because ...) → no ... ; (true because p) → t }
        -- since we always add one variable to the scope of t the uncompared terms
        -- are always at index 2k+1 and k
        genCase : Term → (Term → Term → Term) → Term → Term
        genCase goalTy _`≟_ t = `case ♯ (2 * k ∸ 1) `≟ ♯ (k ∸ 1)
          returning goalTy
          of clauseExprToPatLam (MatchExpr
          ( (singlePatternFromPattern (vArg (``yes' (` 0))) , inj₂ (just t))
          ∷ (singlePatternFromPattern (vArg (``no'  (` 0))) , inj₂ (just (`no $
              -- case ¬p of λ where (ofⁿ ¬p) refl → ¬p refl
              `case ♯ 0 of clauseExprToPatLam (multiClauseExpr
                [(     singlePatternFromPattern (vArg (quote ofⁿ ◇⟦ ` 0 ⟧))
                  NE.∷ singlePatternFromPattern (vArg ``refl) ∷ []
                  , inj₂ (just ♯ 0 ⟦ `refl ⟧)) ]))))
          ∷ []))

        -- yes (case p₁ , ... , pₖ of λ where (ofʸ refl , ... , ofʸ refl) → refl)
        genTrueCase : Term
        genTrueCase = `yes $
          `case NE.foldl₁ (quote _,′_ ∙⟦_∣_⟧) (NE.map ♯ vars)
           of clauseExprToPatLam (MatchExpr
             [ (singlePatternFromPattern
                 (vArg (NE.foldl₁ (quote _,_ ◇⟦_∣_⟧) (NE.map (λ _ → quote ofʸ ◇⟦ ``refl ⟧) vars)))
             , inj₂ (just `refl)) ])

    toMapDiag : SinglePattern → SinglePattern → NE.List⁺ SinglePattern × TC (ClauseExpr ⊎ Maybe Term)
    toMapDiag p@(_ , arg _ p₁) p'@(_ , arg _ p₂) =
      (p NE.∷ [ p' ] , finishMatch (if ⌊ p₁ ≟-Pattern p₂ ⌋ then genBranch (just p) else genBranch nothing))

module _ ⦃ _ : TCOptions ⦄ where
  derive-DecEq : List (Name × Name) → UnquoteDecl
  derive-DecEq = derive-Class 0 (λ transName ps → cartesianProductWith (toMapDiag transName) ps ps)

private
  open import Tactic.Derive.TestTypes
  open import Tactic.Defaults

  unquoteDecl DecEq-These = derive-DecEq [ (quote These , DecEq-These) ]

  unquoteDecl DecEq-⊎ = derive-DecEq [ (quote _⊎_ , DecEq-⊎) ]

  unquoteDecl DecEq-Bool DecEq-ℤ DecEq-List DecEq-Maybe DecEq-ℕ DecEq-Sign DecEq-⊤ = derive-DecEq ((quote Bool , DecEq-Bool) ∷ (quote ℤ , DecEq-ℤ) ∷ (quote List , DecEq-List) ∷ (quote Maybe , DecEq-Maybe) ∷ (quote ℕ , DecEq-ℕ) ∷ (quote Sign , DecEq-Sign) ∷ (quote ⊤ , DecEq-⊤) ∷ [])

  unquoteDecl DecEq-Fin = derive-DecEq [ (quote Fin , DecEq-Fin) ]

  -- this doesn't work since the clause builder machinery doesn't deal
  -- with absurd patterns yet

  --unquoteDecl DecEq-Vec = derive-DecEq [ (quote Vec , DecEq-Vec) ]

  unquoteDecl DecEq-E1 = derive-DecEq [ (quote E1 , DecEq-E1) ]
  unquoteDecl DecEq-E2 = derive-DecEq [ (quote E2 , DecEq-E2) ]

  -- this uses mutual recursion with List E3
  unquoteDecl DecEq-E3 = derive-DecEq [ (quote E3 , DecEq-E3) ]
  -- unquoteDecl DecEq-E4 = derive-DecEq [ (quote E4 , DecEq-E4) ]

  unquoteDecl DecEq-R1 = derive-DecEq [ (quote R1 , DecEq-R1) ]
  unquoteDecl DecEq-R2 = derive-DecEq [ (quote R2 , DecEq-R2) ]
  unquoteDecl DecEq-R20 = derive-DecEq [ (quote R20 , DecEq-R20) ]

  unquoteDecl DecEq-M₁ DecEq-M₂ = derive-DecEq $ (quote M₁ , DecEq-M₁) ∷ (quote M₂ , DecEq-M₂) ∷ []

  -- Expected: DecEq-Term DecEq-Product
