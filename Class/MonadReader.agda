{-# OPTIONS --safe --without-K #-}

module Class.MonadReader where

open import Meta.Prelude

open import Class.Core
open import Class.Functor
open import Class.Applicative
open import Class.Monad
open import Class.MonadError

open MonadError ⦃...⦄

record MonadReader (R : Set ℓ) (M : Type↑) ⦃ _ : Monad M ⦄ : Setω where
  field
    ask : M R
    local : ∀ {a} {A : Set a} → (R → R) → M A → M A

  reader : ∀ {a} {A : Set a} → (R → A) → M A
  reader f = f <$> ask

open MonadReader ⦃...⦄

ReaderT : (R : Set) (M : ∀ {a} → Set a → Set a) → ∀ {a} → Set a → Set a
ReaderT R M A = R → M A

module _ {R : Set} {M : ∀ {a} → Set a → Set a} where

  Functor-ReaderT : ⦃ Functor M ⦄ → Functor (ReaderT R M)
  Functor-ReaderT ._<$>_ f ra r = f <$> ra r

  instance _ = Functor-ReaderT

  Applicative-ReaderT : ⦃ Applicative M ⦄ → Applicative (ReaderT R M)
  Applicative-ReaderT .pure a = const (pure a)
  Applicative-ReaderT ._<*>_ rf ra r = rf r <*> ra r

  instance _ = Applicative-ReaderT

  Monad-ReaderT : ⦃ Monad M ⦄ → Monad (ReaderT R M)
  Monad-ReaderT .return a _ = return a
  Monad-ReaderT ._>>=_ x f r = x r >>= flip f r

  instance _ = Monad-ReaderT

  MonadReader-ReaderT : ⦃ _ : Monad M ⦄ → MonadReader R (ReaderT R M)
  MonadReader-ReaderT .ask r = return r
  MonadReader-ReaderT .local f x = x ∘ f

  MonadError-ReaderT : ∀ {e} {E : Set e} → ⦃ MonadError E M ⦄ → MonadError E (ReaderT R M)
  MonadError-ReaderT .error e _ = error e
  MonadError-ReaderT .catch x h r = catch (x r) (flip h r)
