module Utils where

open import Data.Bool hiding (_≟_)
open import Data.Nat
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

isDecidable : {P : Set} → Dec P → Bool
isDecidable = ⌊_⌋

isEq : ℕ → ℕ → Bool
isEq x y = ⌊ x ≟ y ⌋
