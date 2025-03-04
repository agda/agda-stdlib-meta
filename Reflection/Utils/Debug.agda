-------------------------------------------------
-- ** Errors, debugging

{-# OPTIONS --safe --without-K #-}
module Reflection.Utils.Debug where

open import Meta.Prelude

import Data.String as Str
open import Data.Fin using (Fin)

open import Reflection hiding (_>>_; _>>=_)
open import Reflection.AST.Term

open import Class.Show
open import Class.Functor
open import Class.Monad
open import Class.Traversable

error : String → TC A
error s = typeError [ strErr s ]

_IMPOSSIBLE_ : TC A
_IMPOSSIBLE_ = error "IMPOSSIBLE"

module Debug (v : String × ℕ) where
  -- i.e. set {-# OPTIONS -v v₁:v₂ #-} to enable such messages in the **debug** buffer.

  print printLn : String → TC ⊤
  print s = debugPrint (v .proj₁) (v .proj₂) [ strErr s ]
  printLn = print ∘ (Str._++ "\n")
  printLns = print ∘ Str.unlines

  printS : ⦃ _ : Show A ⦄ → A → TC ⊤
  printS = print ∘ show

  errorP : String → TC A
  errorP s = printLn s >> error s

  printTerm : String → Term → TC ⊤
  printTerm s t = do
    ty ← inferType t
    printLns
      ( (s Str.++ ": {")
      ∷ showTerm ty
      ∷ " ∋ "
      ∷ showTerm t
      ∷ "}\n"
      ∷ [])

  printContext : Telescope → TC ⊤
  printContext ctx = do
    print "\t----CTX----"
    void $ traverse go (enumerate ctx)
    where
      go : ℕ × String × Arg Type → TC ⊤
      go (i , s , ty) = print $
        "\t#" Str.++ show i Str.++ " " Str.++ s Str.++ " : " Str.++ show ty

  printCurrentContext : TC ⊤
  printCurrentContext = printContext =<< getContext

  -- ** definitions
  genSimpleDef : Name → Type → Term → TC ⊤
  genSimpleDef n ty e = do
    print "Generaring..."
    declareDef (vArg n) ty
    print $ "```\n" Str.++ showName n Str.++ " : "
     Str.++ " " Str.++ showTerm ty
    defineFun n [ clause [] [] e ]
    print $ showName n Str.++ " = " Str.++ " "
     Str.++ showTerm e Str.++ "\n```"

module DebugI (v : String) where
  -- i.e. set {-# OPTIONS -v ⟨v⟩:0 #-} to enable messages in the **info** buffer.
  open Debug (v , 0) public

-- set {-# OPTIONS -v trace:100 #-} when tracing
macro
  trace : ∀ {A : Set} ⦃ _ : Show A ⦄ → A → Term → Term → TC ⊤
  trace x t hole = print ("trace: " Str.++ show x) >> unify hole t
    where open Debug ("trace" , 100)
