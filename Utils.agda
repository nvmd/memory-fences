module Utils where

open import Data.List
open import Data.Maybe
open import Data.Product

open import Relation.Binary.Core
open import Relation.Nullary.Decidable

open import Data.Fin
open import Relation.Binary.PropositionalEquality as PropEq
                                                  using (_≡_; refl)
open import Function using (_∘_)
open import Relation.Nullary.Core

head : {X : Set} → List X → Maybe X
head []       = nothing
head (x ∷ xs) = just x

unzip : {X Y : Set} → List (X × Y) → List X × List Y
unzip []             = [] , []
unzip ((x , y) ∷ xs) = x ∷ rx , y ∷ ry
                     where uz = unzip xs
                           rx = proj₁ uz
                           ry = proj₂ uz


{-
infix 4 _≟Fin_

_≟Fin_ : ∀ {n} → Decidable {A = Fin n} {B = Fin n} _≡_
zero  ≟Fin zero   = yes refl
suc m ≟Fin suc n  with m ≟Fin n
suc m ≟Fin suc .m | yes refl = yes refl
suc m ≟Fin suc n  | no prf   = no {! prf ∘ PropEq.cong pred !}
zero  ≟Fin suc n  = no λ()
suc m ≟Fin zero   = no λ()
-}

-- doesn't typecheck though is equivalent to lookup₀(!)
{-
lookup₁ : {X Y : Set} → Decidable {A = X} {B = X} _≡_ → List (X × Y) → X → Maybe Y
lookup₁ d xs q = head (proj₂ (unzip (filter p xs)))
            where p : {X Y : Set} → X × Y → Bool
--                  p = λ x → ⌊ d (proj₁ x) q ⌋
--                  p (x , y) = ⌊ d x q ⌋
-}

lookup : {X Y : Set} → Decidable {A = X} {B = X} _≡_ → List (X × Y) → X → Maybe Y
lookup d xs q = let p = λ x → ⌊ d (proj₁ x) q ⌋
                 in head (proj₂ (unzip (filter p xs)))
