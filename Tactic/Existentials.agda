{-# OPTIONS --safe --without-K #-}
module Tactic.Existentials where

open import Meta.Prelude

open import Reflection hiding (_>>=_; _>>_; _≟_)
open import Reflection.Syntax
open import Reflection.Tactic
open import Reflection.Utils

open import Class.Functor
open import Class.Monad

mkExistential : ℕ → Name → TC Term
mkExistential lvl t = do
  ty ← getType t
  let n = length (argTys ty) ∸ lvl
  return $ go n n
  where
    go : ℕ → ℕ → Term
    go n₀ 0       = def t (fmap (λ n → vArg (♯ n)) (reverse $ upTo n₀))
    go n₀ (suc n) = quote ∃ ∙⟦ (`λ "_" ⇒ go n₀ n) ⟧

macro
  mk∃ : Name → Tactic
  mk∃ t hole = mkExistential 0 t >>= unify hole

private
  data X : ℕ → String → ℕ → Set where
    mkX : X 0 "" 1

  _ : mk∃ X
  _ = 0 , "" , 1 , mkX

  module _ (n : ℕ) where
    data Y : String → ℕ → Set where
      mkY : Y "" 1

    _ : mk∃ Y
    _ = "" , 1 , mkY

    module _ (s : String) where

      data Z : ℕ → Set where
        mkZ : Z 1

      _ : mk∃ Z
      _ = 1 , mkZ

    _ : mk∃ Z
    _ = "sth" , 1 , mkZ

  _ : mk∃ Y
  _ = 42 , "" , 1 , mkY

  _ : mk∃ Z
  _ = 0 , "sth" , 1 , mkZ
