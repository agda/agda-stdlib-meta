{-# OPTIONS --safe --without-K #-}

open import Meta.Prelude

open import Class.Functor
open import Class.Applicative
open import Class.Monad
open import Reflection using (TC; ErrorPart; typeError; catchTC; strErr)

module Class.MonadError where

private variable e f : Level

record MonadError (E : Set e) (M : ∀ {f} → Set f → Set f) : Setω where
  field
    error : E → M A
    catch : M A → (E → M A) → M A

open MonadError

MonadError-TC : MonadError (List ErrorPart) TC
MonadError-TC .error = typeError
MonadError-TC .catch x h = catchTC x (h [ strErr "TC doesn't provide which error to catch" ])

ErrorT : (E : Set) → (M : ∀ {f} → Set f → Set f) → ∀ {f} → Set f → Set f
ErrorT E M A = M (E ⊎ A)

import Data.Sum as Sum

module _ {E : Set} {M : ∀ {a} → Set a → Set a} where

  Functor-ErrorT :  ⦃ _ : Functor M ⦄ → Functor (ErrorT E M)
  Functor-ErrorT ._<$>_ f = fmap (Sum.map₂ f)

  instance _ =  Functor-ErrorT

  Applicative-ErrorT : ⦃ _ : Applicative M ⦄ → Applicative (ErrorT E M)
  Applicative-ErrorT .pure a = pure (inj₂ a)
  Applicative-ErrorT ._<*>_ f x = _<*>_ {F = M} (fmap go f) x
    where
    go : (E ⊎ (A → B)) → (E ⊎ A) → (E ⊎ B)
    go = λ where
      (inj₁ e) _ → inj₁ e
      _ (inj₁ e) → inj₁ e
      (inj₂ f) (inj₂ a) → inj₂ (f a)

  instance _ =  Applicative-ErrorT

  Monad-ErrorT : ⦃ _ : Monad M ⦄ → Monad (ErrorT E M)
  Monad-ErrorT .return a = return (inj₂ a)
  Monad-ErrorT ._>>=_ x f = x >>= λ where
    (inj₁ e) → return (inj₁ e)
    (inj₂ a) → f a

  instance _ =  Monad-ErrorT

  MonadError-ErrorT : ⦃ _ : Monad M ⦄ → MonadError E (ErrorT E M)
  MonadError-ErrorT .error e = return (inj₁ e)
  MonadError-ErrorT .catch x h = x >>= Sum.[ h , return ]
