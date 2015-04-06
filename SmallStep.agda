{-# OPTIONS --allow-unsolved-metas #-}

module SmallStep where

open import X86TSO

open import Data.Bool
open import Data.Nat renaming (_≟_ to _≟ℕ_)
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Empty
open import Relation.Nullary.Decidable

-- 〈 --- \langle
-- 〉 --- \rangle
-- ⊕ --- \oplus
-- ⊗ --- \otimes
-- ⊢ --- \vdash

infix 3 _⊢_⟶e_
infix 3 _⊢_⟶_
infix 3 _⟶_




------------------------------------------------------------------------
-- Expression semantics

data _⊢_⟶e_ (t : Thr) : {y : Ty} → GlobCfg × LocCfgExp t y → GlobCfg × LocCfgExp t y → Set where

  ⟶‵L : ∀ {ls gm lm rc wc x}
    → t ⊢ 〈 ls / gm 〉 , 〈 ` L x / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 C (lm x) / lm / rc / wc 〉

  -- t can read x from memory if t is not blocked, has no buffered writes to x, and the memory does contain x:
  -- not blocked -> no pending ops -> {x is in read cache -> read from read cache; x isn't in read cache -> read from the memory and update read cache} ∎
  ⟶‵Grcmem : ∀ {ls gm lm rc wc x}
    → notBlocked ls t
    → noPendingOps wc x
    → t ⊢ 〈 ls / gm 〉 , 〈 ` G x / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , let z = (lookup rc x) in 〈 maybe′ C (C (gm x)) z / lm / maybe′ (λ _ → rc) (update rc x (gm x)) z / wc 〉

  -- t can read x from its write buffer if t is not blocked and has the newest write to x in its buffer:
  -- not blocked -> x is write cache -> read x from write cache ∎
  ⟶‵Gwc : ∀ {ls gm lm rc wc x}
    → notBlocked ls t
    → thereArePendingOps wc x -- do we really need this to distinguish `Gwc (this) case from `Grcmem?
                              -- yes, because we need to succed with lookup from wc, otherwice it would be `Grcmem case
    → t ⊢ 〈 ls / gm 〉 , 〈 ` G x / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 maybe′ C (C (gm x)) (lookup wc x) / lm / rc / wc 〉

  ⟶⊕ : ∀ {ls gm lm rc wc} → {c₁ c₂ : Val I}
    → t ⊢ 〈 ls  / gm  〉 , 〈 (C c₁) ⊕ (C c₂) / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 C (c₁ + c₂) / lm / rc / wc 〉
  ⟶⊕r : ∀ {ls gm lm rc rc′ wc wc'} → {e₁ e₁' e₂ : Exp t I}
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁' / lm / rc′ / wc' 〉
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ ⊕ e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁' ⊕ e₂ / lm / rc′ / wc' 〉
  ⟶⊕l : ∀ {ls gm lm rc wc rc′ wc'} → {e₁ e₂ e₂' : Exp t I}
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₂' / lm / rc′ / wc' 〉
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ ⊕ e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁ ⊕ e₂' / lm / rc′ / wc' 〉

  ⟶⊗ : ∀ {ls gm lm rc wc} → {c₁ c₂ : Val I}
    → t ⊢ 〈 ls  / gm  〉 , 〈 (C c₁) ⊗ (C c₂) / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 C (c₁ * c₂) / lm / rc / wc 〉
  ⟶⊗r : ∀ {ls gm lm rc rc′ wc wc'} → {e₁ e₁' e₂ : Exp t I}
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁' / lm / rc′ / wc' 〉
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ ⊗ e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁' ⊗ e₂ / lm / rc′ / wc' 〉
  ⟶⊗l : ∀ {ls gm lm rc wc rc′ wc'} → {e₁ e₂ e₂' : Exp t I}
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₂' / lm / rc′ / wc' 〉
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ ⊗ e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁ ⊗ e₂' / lm / rc′ / wc' 〉

  ⟶== : ∀ {ls gm lm rc wc} → {c₁ c₂ : Val I}
    → t ⊢ 〈 ls  / gm  〉 , 〈 (C c₁) == (C c₂) / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 C (⌊ c₁ ≟ℕ c₂ ⌋) / lm / rc / wc 〉
  ⟶==r : ∀ {ls gm lm rc rc′ wc wc'} → {e₁ e₁' e₂ : Exp t I}
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁' / lm / rc′ / wc' 〉
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ == e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁' == e₂ / lm / rc′ / wc' 〉
  ⟶==l : ∀ {ls gm lm rc wc rc′ wc'} → {e₁ e₂ e₂' : Exp t I}
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₂' / lm / rc′ / wc' 〉
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ == e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁ == e₂' / lm / rc′ / wc' 〉


------------------------------------------------------------------------
-- Statement semantics

data _⊢_⟶_ (t : Thr) : GlobCfg × LocCfg t → GlobCfg × LocCfg t → Set where

  ⟶:=Local₀ : ∀ {ls gm x lm rc wc c}
    → t ⊢ 〈 ls / gm 〉 , 〈 just (L x := (C c)) / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / updateMem lm x c / rc / wc 〉

  ⟶:=Local₁ : ∀ {ls gm x e lm rc wc ls′ gm′ e′ lm′ rc′}
    → t ⊢ 〈 ls / gm 〉 , 〈 e / lm / rc / wc 〉 ⟶e 〈 ls′ / gm′ 〉 , 〈 e′ / lm′ / rc′ / wc 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (L x := e) / lm / rc / wc 〉 ⟶ 〈 ls′ / gm′ 〉 , 〈 just (L x := e′) / lm′ / rc′ / wc 〉

  ⟶:=Global₀ : ∀ {ls gm x lm rc wc c}
    → t ⊢ 〈 ls / gm 〉 , 〈 just (G x := (C c)) / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / lm / rc / update wc x c 〉

  ⟶:=Global₁ : ∀ {ls gm x e lm rc wc ls′ gm′ e′ lm′ rc′}
    → t ⊢ 〈 ls / gm 〉 , 〈 e / lm / rc / wc 〉 ⟶e 〈 ls′ / gm′ 〉 , 〈 e′ / lm′ / rc′ / wc 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (G x := e) / lm / rc / wc 〉 ⟶ 〈 ls′ / gm′ 〉 , 〈 just (G x := e′) / lm′ / rc′ / wc 〉

  ⟶Skip : ∀ {ls gm lm rc wc}
    → t ⊢ 〈 ls / gm 〉 , 〈 just Skip / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / lm / rc / wc 〉

  ⟶\\₀ : ∀ {ls gm s s1 lm rc wc ls' gm' lm' rc' wc'}
    → t ⊢ 〈 ls / gm 〉 , 〈 just s / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 nothing  / lm' / rc' / wc' 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (s \\ s1) / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just s1  / lm' / rc' / wc' 〉

  ⟶\\₁ : ∀ {ls gm s s1 lm rc wc ls' gm' s' lm' rc' wc'}
    → t ⊢ 〈 ls / gm 〉 , 〈 just s / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just s'  / lm' / rc' / wc' 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (s \\ s1) / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just (s' \\ s1)  / lm' / rc' / wc' 〉

  ⟶IfThenElse₀ : ∀ {ls gm lm rc wc c s₀ s₁}
    → t ⊢ 〈 ls / gm 〉 , 〈 just (If (C c) Then s₀ Else s₁) / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 just (if c then s₀ else s₁) / lm / rc / wc 〉

  ⟶IfThenElse₁ : ∀ {ls ls′ gm gm′ lm lm′ rc rc′ wc e e′ s₀ s₁}
    → t ⊢ 〈 ls / gm 〉 , 〈 e / lm / rc / wc 〉 ⟶e 〈 ls′ / gm′ 〉 , 〈 e′ / lm′ / rc′ / wc 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (If e Then s₀ Else s₁) / lm / rc / wc 〉 ⟶ 〈 ls′ / gm′ 〉 , 〈 just (If e′ Then s₀ Else s₁) / lm′ / rc′ / wc 〉

  ⟶WhileDo : ∀ {ls gm lm rc wc cond stmt}
    → t ⊢ 〈 ls / gm 〉 , 〈 just (While cond Do stmt) / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 just (If cond Then (stmt \\ While cond Do stmt) Else Skip) / lm / rc / wc 〉

  ⟶Lock : ∀ {gm lm rc}
    → t ⊢ 〈 nothing / gm 〉 , 〈 just Lock / lm / rc / [] 〉 ⟶ 〈 just t / gm 〉 , 〈 nothing / lm / rc / [] 〉

  ⟶Unlock : ∀ {gm lm rc}
    → t ⊢ 〈 just t / gm 〉 , 〈 just Unlock / lm / rc / [] 〉 ⟶ 〈 nothing / gm 〉 , 〈 nothing / lm / rc / [] 〉

  ⟶LFence : ∀ {ls gm lm wc}
    → t ⊢ 〈 ls / gm 〉 , 〈 just LFence / lm / [] / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / lm / [] / wc 〉

  ⟶SFence : ∀ {ls gm lm rc}
    → t ⊢ 〈 ls / gm 〉 , 〈 just SFence / lm / rc / [] 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / lm / rc / [] 〉

  ⟶Dequeue : ∀ {ls gm s lm rc wc wc'}
    → notBlocked ls t
    → wc ⇒ wc'
    → t ⊢ 〈 ls / gm 〉 , 〈 s / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 s / lm / rc / wc' 〉


------------------------------------------------------------------------
-- System semantics

data _⟶_ : GlobCfg × LocCfgs → GlobCfg × LocCfgs → Set where
   step : (t : Thr) → ∀ {ls gm lcfgs ls' gm' lcfgs'}
          → t ⊢ 〈 ls / gm 〉 , lcfgs t ⟶ 〈 ls' / gm' 〉 , lcfgs' t
          → ((t' : Thr) → t ≢ t' → lcfgs t' ≡ lcfgs' t')
          → 〈 ls / gm 〉 , lcfgs ⟶ 〈 ls' / gm' 〉 , lcfgs'
