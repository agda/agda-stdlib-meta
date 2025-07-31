{-# OPTIONS --safe --without-K #-}

module Reflection.Syntax where

open import Meta.Prelude

open import Reflection.AST.Definition public
  using (Definition; function; data-type; axiom; record′; constructor′; primitive′)
open import Reflection.AST.Pattern public
  using (Pattern; con; dot; var; lit; proj; absurd)
open import Reflection.AST.Term public
  using ( Term; pi; var; con; def; lam; pat-lam; sort; lit; meta; unknown
        ; vLam; hLam; iLam; Π[_∶_]_; vΠ[_∶_]_; hΠ[_∶_]_; iΠ[_∶_]_
        ; Type; Telescope
        ; Sort; set; prop; propLit; inf
        ; Clause; Clauses; clause; absurd-clause
        )
open import Reflection.AST.Abstraction public
  using (Abs; abs; unAbs)
open import Reflection.AST.Argument public
  using (Arg; Args; arg; vArg; hArg; iArg; unArg; _⟨∷⟩_; map-Args)
open import Reflection.AST.Literal public
  using (Literal)
open import Reflection.AST.Meta public
  using (Meta)
open import Reflection.AST.Name public
  using (Name)
open import Reflection.AST.Argument.Visibility public
  using (Visibility; visible; hidden; instance′)
open import Reflection.AST.Argument.Information public
  using (ArgInfo; arg-info)
open import Reflection.AST.Argument.Modality public
  using (Modality; modality)
open import Reflection.AST.Argument.Relevance public
  using (Relevance; relevant; irrelevant)
open import Reflection public
  using (ErrorPart; strErr)

open import Reflection using (TC)

-- ** Smart constructors

-- arguments
pattern hArg? = hArg unknown
pattern vArg? = vArg unknown
pattern iArg? = iArg unknown

-- variables
pattern ♯ n = var n []
pattern ♯_⟦_⟧ n x = var n (vArg x ∷ [])
pattern ♯_⟦_∣_⟧ n x y = var n (vArg x ∷ vArg y ∷ [])

-- patterns
pattern `_ x = Pattern.var x
pattern `∅   = Pattern.absurd 0

-- clauses
pattern ⟦⦅_⦆∅⟧ tel = absurd-clause tel (vArg `∅ ∷ [])
pattern ⟦∅⟧ = absurd-clause [] (vArg `∅ ∷ [])

pattern ⟦⇒_⟧ k = clause [] [] k
pattern ⟦⦅_⦆⇒_⟧ tel k = clause tel [] k

pattern ⟦_⇒_⟧ x k = clause [] (vArg x ∷ []) k
pattern ⟦_⦅_⦆⇒_⟧ x tel k = clause tel (vArg x ∷ []) k

pattern ⟦_∣_⇒_⟧ x y k = clause [] (vArg x ∷ vArg y ∷ []) k
pattern ⟦_∣_⦅_⦆⇒_⟧ x y tel k = clause tel (vArg x ∷ vArg y ∷ []) k

pattern ⟦_∣_∣_⇒_⟧ x y z k = Clause.clause [] (vArg x ∷ vArg y ∷ vArg z ∷ []) k
pattern ⟦_∣_∣_⦅_⦆⇒_⟧ x y z tel k = Clause.clause tel (vArg x ∷ vArg y ∷ vArg z ∷ []) k

-- lambdas
pattern `λ_⇒_       x     k = lam visible (abs x k)
pattern `λ⟦_∣_⇒_⟧   x y   k = `λ x ⇒ `λ y ⇒ k
pattern `λ⟦_∣_∣_⇒_⟧ x y z k = `λ x ⇒ `λ y ⇒ `λ z ⇒ k

pattern `λ⟅_⟆⇒_     x k = lam hidden (abs x k)
pattern `λ⦃_⦄⇒_     x k = lam instance′ (abs x k)

pattern `λ⦅_⦆∅ tel = pat-lam (⟦⦅ tel ⦆∅⟧ ∷ []) []
pattern `λ∅ = pat-lam (⟦∅⟧ ∷ []) []

pattern `λ⟦_⇒_⟧ p k = pat-lam (⟦ p ⇒ k ⟧ ∷ []) []
pattern `λ⟦_⦅_⦆⇒_⟧ p tel k = pat-lam (⟦ p ⦅ tel ⦆⇒ k ⟧ ∷ []) []

pattern `λ⟦_⇒_∣_⇒_⟧ p₁ k₁ p₂ k₂ = pat-lam (⟦ p₁ ⇒ k₁ ⟧ ∷ ⟦ p₂ ⇒ k₂ ⟧ ∷ []) []
pattern `λ⟦_⦅_⦆⇒_∣_⦅_⦆⇒_⟧ p₁ tel₁ k₁ p₂ tel₂ k₂ = pat-lam (⟦ p₁ ⦅ tel₁ ⦆⇒ k₁ ⟧ ∷ ⟦ p₂ ⦅ tel₂ ⦆⇒ k₂ ⟧ ∷ []) []

-- function application
pattern _∙ n = def n []
pattern _∙⟦_⟧ n x = def n (vArg x ∷ [])
pattern _∙⟦_∣_⟧ n x y = def n (vArg x ∷ vArg y ∷ [])
pattern _∙⟦_∣_∣_⟧ n x y z = def n (vArg x ∷ vArg y ∷ vArg z ∷ [])
pattern _∙⟦_∣_∣_∣_⟧ n x y z w = def n (vArg x ∷ vArg y ∷ vArg z ∷ vArg w ∷ [])

pattern _◆ n = con n []
pattern _◆⟦_⟧ n x = con n (vArg x ∷ [])
pattern _◆⟦_∣_⟧ n x y = con n (vArg x ∷ vArg y ∷ [])

pattern _◇ n = Pattern.con n []
pattern _◇⟦_⟧ n x = Pattern.con n (vArg x ∷ [])
pattern _◇⟦_∣_⟧ n x y = Pattern.con n (vArg x ∷ vArg y ∷ [])

pattern `Set = sort (set (quote 0ℓ ∙))

-- ** useful type aliases
PatTelescope = Telescope
Context      = Args Type
TTerm        = Term × Type
Hole         = Term
THole        = Hole × Type
