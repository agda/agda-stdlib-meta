{-# OPTIONS --safe --without-K #-}

module Tactic.Solver.Core.Tests where

open import Agda.Primitive using (lzero)
open import Data.Fin using (Fin; fromℕ)
import Data.Fin.Reflection as Fin
open import Data.List using (List; []; _∷_; length; lookup; foldr)
import Data.List.Reflection as List
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Reflection
open import Reflection.AST.Argument
open import Reflection.TCM.Syntax

open import Tactic.Solver.Core

private
  alias : ℕ → ℕ
  alias n = n

  sameAtom : (atoms : List ℕ) (i j : Fin (length atoms)) → i ≡ j
           → lookup atoms i ≡ lookup atoms j
  sameAtom atoms i .i refl = refl

  indexTheory : DetectedTheory
  indexTheory = record
    { operators = []
    ; constants = []
    ; literalSpec = nothing
    ; blockedNames = []
    ; sortOf = nothing
    ; atomEmission = binder
    ; encodeEq = λ _ x _ → x
    ; finishSolve = λ _ x _ → x
    }

  theory : TwoLevelTheory
  theory = record
    { macroName = "same-atom"
    ; indexTheory = indexTheory
    ; prepIndex = pure
    ; operators = []
    ; blockedNames = []
    ; atomRef = λ _ i → Fin.toTerm (fromℕ i)
    ; matchType = λ where
        (def (quote ℕ) []) → just []
        _ → nothing
    ; encodeSig = λ _ atom _ → atom
    ; finishSolve = λ _ i j _ atoms → def (quote sameAtom)
        (vArg (foldr List._`∷_ List.`[] atoms) ∷ vArg i ∷ vArg j
        ∷ vArg (con (quote refl) []) ∷ [])
    }

  macro
    solveAlias : Term → TC ⊤
    solveAlias hole = do
      -- Construct the goal explicitly so elaboration cannot erase the alias
      -- before the frontend sees its two definitionally equal spellings.
      let n = var 0 []
          a = def (quote alias) (vArg n ∷ [])
          ty = def (quote _≡_)
            (hArg (quoteTerm lzero) ∷ hArg (quoteTerm ℕ) ∷ vArg a ∷ vArg n ∷ [])
      h ← newMeta ty
      solveByTwoLevelTheory theory (quoteTerm 0) h
      unify hole h

alias-identity : (n : ℕ) → alias n ≡ n
alias-identity n = solveAlias
