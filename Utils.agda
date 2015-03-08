module Utils where

open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Relation.Nullary.Core

isDecidable : {P : Set} → Dec P → Bool
isDecidable (yes p) = true
isDecidable (no ¬p) = false

isEq : ℕ → ℕ → Bool
isEq x y = isDecidable (x ≟ y)
