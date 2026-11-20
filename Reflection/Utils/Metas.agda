{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Metas where

open import Meta.Prelude
open import Meta.Init

import Data.Bool.ListAction as B
import Reflection.AST.Meta as Meta
import Reflection.AST.Traversal as Traversal
open import Effect.Applicative

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
firstMeta = head ∘ findMetaIds

shareMeta : List Meta → List Meta → Bool
shareMeta xs ys = B.any (λ x → B.any (Meta._≡ᵇ_ x) ys) xs

-- does the term have metas?
metaFree : Term → Bool
metaFree = traverseTerm (record defaultActions { onMeta = λ _ _ → false }) (0 , [])
  where
    allApplicative : RawApplicative (λ (_ : Set) → Bool)
    allApplicative = mkRawApplicative _ (λ _ → true) _∧_

    open Traversal allApplicative
