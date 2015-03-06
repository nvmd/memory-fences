module SmallStepLemmas where

open import X86TSO
open import SmallStep

open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Empty

lemma-const-non-eval : {t : Thr} {y : Ty} {c : Val y} → ∀ {g1 g2 lm rc wc lm' rc' wc'} → t ⊢ g1 , 〈 C c / lm / rc / wc 〉 ⟶e g2 , 〈 C c / lm' / rc' / wc' 〉 → ⊥
lemma-const-non-eval {g1 = 〈 lockSt / globMem 〉} {〈 lockSt₁ / globMem₁ 〉} ()

lemma-wc-nonupdate : {t : Thr} {y : Ty} {e e' : Exp t y} → ∀ {g1 g2 lm rc wc lm' rc' wc'} → t ⊢ g1 , 〈 e / lm / rc / wc 〉 ⟶e g2 , 〈 e' / lm' / rc' / wc' 〉 → wc ≡ wc'
lemma-wc-nonupdate {g1 = 〈 lockSt / globMem 〉} {〈 .lockSt / .globMem 〉} ⟶‵L = refl
lemma-wc-nonupdate {g1 = 〈 lockSt / globMem 〉} {〈 .lockSt / .globMem 〉} ⟶‵G = refl
lemma-wc-nonupdate {g1 = 〈 lockSt / globMem 〉} {〈 .lockSt / .globMem 〉} ⟶⊕ = refl
lemma-wc-nonupdate {g1 = 〈 lockSt / globMem 〉} {〈 .lockSt / .globMem 〉} (⟶⊕r d) = lemma-wc-nonupdate d
lemma-wc-nonupdate {g1 = 〈 lockSt / globMem 〉} {〈 .lockSt / .globMem 〉} (⟶⊕l d) = lemma-wc-nonupdate d
