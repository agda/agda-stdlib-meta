-- Deriving show.

{-# OPTIONS -v allTactics:100 #-}
{-# OPTIONS --safe #-}
module Tactic.Derive.Show where

open import Meta.Prelude
open import Meta.Init

open import Agda.Builtin.Reflection using (primShowQName)

import Data.List as L
import Data.List.NonEmpty as NE
import Reflection as R
open import Data.String using (fromList; toList) renaming (_++_ to _++S_)
open import Reflection.Tactic
open import Relation.Nullary.Negation
open import Relation.Nullary.Decidable

open import Class.DecEq
open import Class.Functor
open import Class.MonadTC.Instances
open import Class.Show.Core
open import Class.Traversable

open import Tactic.ClauseBuilder
open import Tactic.Derive (quote Show) (quote show)

instance
  _ = ContextMonad-MonadTC

open ClauseExprM

sLit = Term.lit ∘ Agda.Builtin.Reflection.Literal.string

showName : Name → String
showName n = let n' = R.showName n in dropModulePrefix n'
  where
    dropModulePrefix : String → String
    dropModulePrefix s = fromList $ reverse $ takeWhile (¬? ∘ ('.' ≟_)) $ reverse $ toList s

wrapWithPars : String → String
wrapWithPars s = "(" ++S s ++S ")"

genPars : Term → Term
genPars t = quote wrapWithPars ∙⟦ t ⟧

module _ (transName : Name → Maybe Name) where
  showFromTerm : Term → Term → Term
  showFromTerm (def n _) t with transName n
  ... | just n'    = def (quote show) (iArg (n' ∙) ∷ vArg t ∷ [])
  ... | nothing    = quote show ∙⟦ t ⟧
  showFromTerm _ t = quote show ∙⟦ t ⟧

  genShow : Name → List Term → Term
  genShow n [] = sLit (showName n)
  genShow n (x ∷ l) = quote _<+>_ ∙⟦ genShow n l ∣ genPars x ⟧

  patternToClause : SinglePattern → NE.List⁺ SinglePattern × TC (ClauseExpr ⊎ Maybe Term)
  patternToClause p@(l , arg _ (Pattern.con n _)) = NE.[ p ] , finishMatch do
    typeList ← traverse ⦃ Functor-List ⦄ (λ t → do T ← inferType t; return (T , t)) (applyDownFrom ♯ (length l))
    return $ genShow n (L.map (uncurry showFromTerm) $ reverse typeList)
  patternToClause p = NE.[ p ] , error1 "Error: not a con!"

module _ ⦃ _ : TCOptions ⦄ where
  derive-Show : List (Name × Name) → UnquoteDecl
  derive-Show = derive-Class 0 (λ transName → L.map (patternToClause transName))

private
  open import Tactic.Derive.TestTypes
  import Data.Nat.Show
  open import Tactic.Defaults
  open import Data.List.Relation.Binary.Pointwise.Base

  unquoteDecl Show-Bool Show-ℤ Show-List Show-Maybe Show-ℕ Show-Sign Show-⊤ = derive-Show ((quote Bool , Show-Bool) ∷ (quote ℤ , Show-ℤ) ∷ (quote List , Show-List) ∷ (quote Maybe , Show-Maybe) ∷ (quote ℕ , Show-ℕ) ∷ (quote Sign , Show-Sign) ∷ (quote ⊤ , Show-⊤) ∷ [])

  unquoteDecl Show-Fin = derive-Show [ (quote Fin , Show-Fin) ]
  unquoteDecl Show-Vec = derive-Show [ (quote Vec , Show-Vec) ]

  unquoteDecl Show-Pointwise = derive-Show [ (quote Pointwise , Show-Pointwise) ]

  unquoteDecl Show-These = derive-Show [ (quote These , Show-These) ]
  unquoteDecl Show-⊎ = derive-Show [ (quote _⊎_ , Show-⊎) ]

  unquoteDecl Show-E1 Show-E2 Show-E3 = derive-Show
    ((quote E1 , Show-E1) ∷ (quote E2 , Show-E2) ∷ (quote E3 , Show-E3) ∷ [])

  -- unquoteDecl Show-E4 = derive-Show [ (quote E4 , Show-E4) ]

  unquoteDecl Show-R1 Show-R2 = derive-Show
    ((quote R1 , Show-R1) ∷ (quote R2 , Show-R2) ∷ [])

  unquoteDecl Show-M₁ Show-M₂ = derive-Show $ (quote M₁ , Show-M₁) ∷ (quote M₂ , Show-M₂) ∷ []

  -- Expected: Show-Product Show-Term
