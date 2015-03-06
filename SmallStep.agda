{-# OPTIONS --allow-unsolved-metas #-}

module SmallStep where

open import X86TSO

open import Data.Bool
open import Data.Nat
open import Data.Product
open import Data.Sum
open import Data.Maybe
open import Data.List
open import Relation.Binary.PropositionalEquality
open import Data.Empty

-- 〈 --- \langle
-- 〉 --- \rangle
-- ⊕ --- \oplus
-- ⊗ --- \otimes
-- ⊢ --- \vdash

infix 3 _⊢_⟶e_
infix 3 _⊢_⟶_
infix 3 _⟶_

postulate update : {X Y : Set} → List (X × Y) → X → Y → List (X × Y)
--update = {!!}

postulate lookup : {X Y : Set} → List (X × Y) → X → Maybe Y
--lookup = {!!}

postulate updateMem : {X Y : Set} → (X → Y) → X → Y → (X → Y)
--updateMem = {!!}

-- Expression small-step semantics
data _⊢_⟶e_ (t : Thr) : {y : Ty} → GlobCfg × LocCfgExp t y → GlobCfg × LocCfgExp t y → Set where
--  ⟶C : ∀ {ls gm lm rc wc y} → {c : Val y}
--    → t ⊢ 〈 ls / gm 〉 , 〈 inj₁ (C c) / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 inj₂ c / lm / rc / wc 〉

  ⟶‵L : ∀ {ls gm lm rc wc x}
    → t ⊢ 〈 ls / gm 〉 , 〈 ` L x / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 C (lm x) / lm / rc / wc 〉

  ⟶‵G : ∀ {ls gm lm rc wc x}
    → t ⊢ 〈 ls / gm 〉 , 〈 ` G x / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , let z = (lookup rc x) in  〈 maybe′ C (C (gm x)) z / lm / maybe′ (λ _ → rc) (update rc x (gm x)) z / wc 〉

  ⟶⊕ : ∀ {ls gm lm rc wc} → {c₁ c₂ : Val I}
    → t ⊢ 〈 ls  / gm  〉 , 〈 (C c₁) ⊕ (C c₂) / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 C (c₁ + c₂) / lm / rc / wc 〉
  ⟶⊕r : ∀ {ls gm lm rc rc′ wc wc'} → {e₁ e₁' e₂ : Exp t I}
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁' / lm / rc′ / wc' 〉
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ ⊕ e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁' ⊕ e₂ / lm / rc′ / wc' 〉
  ⟶⊕l : ∀ {ls gm lm rc wc rc′ wc'} → {e₁ e₂ e₂' : Exp t I}
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₂' / lm / rc′ / wc' 〉
     → t ⊢ 〈 ls  / gm  〉 , 〈 e₁ ⊕ e₂ / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 e₁ ⊕ e₂' / lm / rc′ / wc' 〉

{-
  ⟶⊗ : ∀ {ls gm lm rc wc}
    → t ⊢ 〈 ls / gm 〉 , 〈 {!!} / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 {!!} / lm / rc / wc 〉
  ⟶== : ∀ {ls gm e₁ e₂ eᵣ lm rc wc v₁ v₂ vᵣ}
    → t ⊢ 〈 ls / gm 〉 , 〈 {!!} / lm / rc / wc 〉 ⟶e 〈 ls / gm 〉 , 〈 {!!} / lm / rc / wc 〉
-}

-- Statement small-step semantics
-- (t : Thr) ⊢ (s₀ : GlobCfg × LocCfg t) ⟶ (s₁ : GlobCfg × LocCfg t) : Set
data _⊢_⟶_ (t : Thr) : GlobCfg × LocCfg t → GlobCfg × LocCfg t → Set where

  ⟶:=LocalConst : ∀ {ls gm x lm rc wc c}
    → t ⊢ 〈 ls / gm 〉 , 〈 just (L x := (C c)) / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / updateMem lm x c / rc / wc 〉

  ⟶:=Local : ∀ {ls gm x e lm rc wc ls′ gm′ e′ lm′ rc′}
    → t ⊢ 〈 ls / gm 〉 , 〈 e / lm / rc / wc 〉 ⟶e 〈 ls′ / gm′ 〉 , 〈 e′ / lm′ / rc′ / wc 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (L x := e) / lm / rc / wc 〉 ⟶ 〈 ls′ / gm′ 〉 , 〈 just (L x := e′) / lm′ / rc′ / wc 〉

  ⟶:=GlobalConst : ∀ {ls gm x lm rc wc c}
    → t ⊢ 〈 ls / gm 〉 , 〈 just (G x := (C c)) / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / lm / rc / update wc x c 〉

  ⟶:=Global : ∀ {ls gm x e lm rc wc ls′ gm′ e′ lm′ rc′}
    → t ⊢ 〈 ls / gm 〉 , 〈 e / lm / rc / wc 〉 ⟶e 〈 ls′ / gm′ 〉 , 〈 e′ / lm′ / rc′ / wc 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (G x := e) / lm / rc / wc 〉 ⟶ 〈 ls′ / gm′ 〉 , 〈 just (G x := e′) / lm′ / rc′ / wc 〉

  ⟶Skip : ∀ {ls gm lm rc wc}
    → t ⊢ 〈 ls / gm 〉 , 〈 just Skip / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / lm / rc / wc 〉

  ⟶\\₁ : ∀ {ls gm s s1 lm rc wc ls' gm' lm' rc' wc'}
    → t ⊢ 〈 ls / gm 〉 , 〈 just s / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 nothing  / lm' / rc' / wc' 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (s \\ s1) / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just s1  / lm' / rc' / wc' 〉

  ⟶\\₂ : ∀ {ls gm s s1 lm rc wc ls' gm' s' lm' rc' wc'}
    → t ⊢ 〈 ls / gm 〉 , 〈 just s / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just s'  / lm' / rc' / wc' 〉
    → t ⊢ 〈 ls / gm 〉 , 〈 just (s \\ s1) / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just (s' \\ s1)  / lm' / rc' / wc' 〉

  ⟶IfThenElseConst : ∀ {ls gm lm rc wc c s₀ s₁}
    → t ⊢ 〈 ls / gm 〉 , 〈 just (If (C c) Then s₀ Else s₁) / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 just (if c then s₀ else s₁) / lm / rc / wc 〉

  ⟶IfThenElse : ∀ {ls ls′ gm gm′ lm lm′ rc rc′ wc e e′ s₀ s₁}
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
             → notblocked ls t
             → wc ⇒ wc'
             → t ⊢ 〈 ls / gm 〉 , 〈 s / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 s / lm / rc / wc' 〉


-- Whole system semantics

data _⟶_ : GlobCfg × LocCfgs → GlobCfg × LocCfgs → Set where
   step : (t : Thr) → ∀ {ls gm lcfgs ls' gm' lcfgs'}
          → t ⊢ 〈 ls / gm 〉 , lcfgs t ⟶ 〈 ls' / gm' 〉 , lcfgs' t
          → ((t' : Thr) → t ≢ t' → lcfgs t' ≡ lcfgs' t')
          → 〈 ls / gm 〉 , lcfgs ⟶ 〈 ls' / gm' 〉 , lcfgs'
