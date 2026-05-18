{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Metas where

open import Meta.Prelude
open import Meta.Init

open import Data.List using (_++_; mapMaybe)

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
    (sort _)      → []
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
    (clause _ _ t      ∷ c) → findMetas t ++ findMetasCl c
    (absurd-clause _ _ ∷ c) → findMetasCl c

metaId : Term → Maybe Meta
metaId (meta x _) = just x
metaId _          = nothing

findMetaIds : Term → List Meta
findMetaIds = mapMaybe metaId ∘ findMetas

firstMeta : Term → Maybe Meta
firstMeta t = case findMetaIds t of λ where
  []      → nothing
  (m ∷ _) → just m
