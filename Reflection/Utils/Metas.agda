{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Metas where

open import Meta.Prelude
open import Meta.Init

open import Data.List using (_++_)

isMeta : Term → Bool
isMeta = λ where
  (meta _ _) → true
  _          → false

mutual
  findMetas : Term → List Term
  findMetas = λ where
    (var _ as) → findMetas* as
    (con _ as) → findMetas* as
    (def _ as) → findMetas* as
    (lam _ (abs _ x)) → findMetas x
    (pat-lam cs as)   → findMetasCl cs ++ findMetas* as
    (pi (arg _ a) (abs _ b)) → findMetas a ++ findMetas b
    (agda-sort _) → []
    (lit _)       → []
    m@(meta x as) → m ∷ findMetas* as
    unknown       → []

  findMetas* : List (Arg Term) → List Term
  findMetas* = λ where
    [] → []
    ((arg _ t) ∷ ts) → findMetas t ++ findMetas* ts

  findMetasCl : List Clause → List Term
  findMetasCl = λ where
    [] → []
    (Clause.clause _ _ t ∷ c)      → findMetas t ++ findMetasCl c
    (Clause.absurd-clause _ _ ∷ c) → findMetasCl c
