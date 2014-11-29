module X86TSO where

open import Data.Fin
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.Product
open import Relation.Binary.PropositionalEquality


record ProgParams : Set where
  field
    #threads : ℕ
    #locals : Fin #threads → ℕ
    #globals : ℕ

postulate params : ProgParams

open ProgParams params

Thr : Set
Thr = Fin #threads

Loc : Thr → Set
Loc t = Fin (#locals t)

Glob : Set
Glob = Fin #globals

Int : Set
Int = ℕ


data Ty : Set where
    I : Ty
    B : Ty

data Var (t : Thr) : Set where
    L : Loc t → Var t
    G : Glob → Var t

data Exp (t : Thr) : Ty → Set where
    `_ : Var t → Exp t I
    _⊕_ : Exp t I → Exp t I → Exp t I
    _⊗_ : Exp t I → Exp t I → Exp t I
    _==_ : Exp t I → Exp t I → Exp t B

data Stmt (t : Thr) : Set where
    _:=_ : Var t → Exp t I → Stmt t
    Skip : Stmt t
    _\\_ : Stmt t → Stmt t → Stmt t
    If_Then_Else_ : Exp t B → Stmt t → Stmt t → Stmt t
    While_Do_ : Exp t B → Stmt t → Stmt t
    Lock : Stmt t
    Unlock : Stmt t
    LFence : Stmt t
    SFence : Stmt t


Val : Ty → Set
Val I = Int
Val B = Bool

LockSt : Set
LockSt = Maybe Thr

GlobMem : Set
GlobMem = Glob → Int

Cache : Set
Cache = List (Glob × Int)

LocMem : Thr → Set
LocMem t = Loc t → Int

record GlobCfg : Set where
  constructor 〈_/_〉
  field
    lockSt : LockSt
    globMem : GlobMem

record LocCfg (t : Thr) : Set where
  constructor 〈_/_/_/_〉
  field
    residStmt : Maybe (Stmt t)
    locMem : LocMem t
    readCache : Cache
    writeCache : Cache

LocCfgs : Set
LocCfgs = (t : Thr) → LocCfg t

notblocked : LockSt → Thr → Set
notblocked nothing  t' = ⊤
notblocked (just t) t' = t ≡ t'

infix 3 _⊢_⟶_
infix 3 _⟶_


_⇒_ : Cache → Cache → Set
_⇒_ = {!!}

data _⊢_⟶e_(t : Thr) : GlobCfg × Exp t I × LocMem t × Cache × Cache → Val I → Set where


data _⊢_⟶_ (t : Thr) : GlobCfg × LocCfg t → GlobCfg × LocCfg t → Set where

  ⟶:=a : ∀ {ls gm x e lm rc wc v lm'}
          → t ⊢ 〈 ls / gm 〉 , e , lm , rc , wc  ⟶e v
          → v ≡ lm' x
          → ((x' : Loc t) →  x ≢ x' → lm x' ≡ lm' x')
          → t ⊢ 〈 ls / gm 〉 , 〈 just (L x := e) / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / lm' / rc / wc 〉


  ⟶Skip : ∀ {ls gm lm rc wc}
          → t ⊢ 〈 ls / gm 〉 , 〈 just Skip / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 nothing / lm / rc / wc 〉

  ⟶\\a : ∀ {ls gm s s1 lm rc wc ls' gm' lm' rc' wc'}
          → t ⊢ 〈 ls / gm 〉 , 〈 just s / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 nothing  / lm' / rc' / wc' 〉
          → t ⊢ 〈 ls / gm 〉 , 〈 just (s \\ s1) / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just s1  / lm' / rc' / wc' 〉

  ⟶\\b : ∀ {ls gm s s1 lm rc wc ls' gm' s' lm' rc' wc'}
          → t ⊢ 〈 ls / gm 〉 , 〈 just s / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just s'  / lm' / rc' / wc' 〉
          → t ⊢ 〈 ls / gm 〉 , 〈 just (s \\ s1) / lm / rc / wc 〉 ⟶ 〈 ls' / gm' 〉 , 〈 just (s' \\ s1)  / lm' / rc' / wc' 〉

  ⟶Lock : ∀ {gm lm rc}
          → t ⊢ 〈 nothing / gm 〉 , 〈 just Lock / lm / rc / [] 〉 ⟶ 〈 just t / gm 〉 , 〈 nothing / lm / rc / [] 〉

  ⟶Unlock : ∀ {gm lm rc}
          → t ⊢ 〈 just t / gm 〉 , 〈 just Unlock / lm / rc / [] 〉 ⟶ 〈 nothing / gm 〉 , 〈 nothing / lm / rc / [] 〉


  ⟶Dequeue : ∀ {ls gm s lm rc wc wc'}
          → notblocked ls t
          → wc ⇒ wc'
          → t ⊢ 〈 ls / gm 〉 , 〈 s / lm / rc / wc 〉 ⟶ 〈 ls / gm 〉 , 〈 s / lm / rc / wc' 〉


data _⟶_ : GlobCfg × LocCfgs → GlobCfg × LocCfgs → Set where
   step : (t : Thr) → ∀ {ls gm lcfgs ls' gm' lcfgs'}
          → t ⊢ 〈 ls / gm 〉 , lcfgs t ⟶ 〈 ls' / gm' 〉 , lcfgs' t
          → ((t' : Thr) → t ≢ t' → lcfgs t' ≡ lcfgs' t')
          → 〈 ls / gm 〉 , lcfgs ⟶ 〈 ls' / gm' 〉 , lcfgs'
