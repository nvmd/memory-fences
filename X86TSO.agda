{-# OPTIONS --allow-unsolved-metas #-}

module X86TSO where

open import Data.Fin hiding (_+_)
open import Data.Nat
open import Data.Unit
open import Data.Empty
open import Data.Bool
open import Data.Maybe
open import Data.List
open import Data.Product
open import Data.Sum
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

--Int : Set
--Int = ℕ

MemAddr : Set
MemAddr = ℕ

data Ty : Set where
    I : Ty
    B : Ty

data Var (t : Thr) : Set where
    L : Loc t → Var t
    G : Glob → Var t

Val : Ty → Set
Val I = ℕ
Val B = Bool

data Exp (t : Thr) : Ty → Set where
    C    : {y : Ty} → Val y → Exp t y
    `_   : Var t → Exp t I
    _⊕_  : Exp t I → Exp t I → Exp t I
    _⊗_  : Exp t I → Exp t I → Exp t I
    _==_ : Exp t I → Exp t I → Exp t B

data Stmt (t : Thr) : Set where
    _:=_          : Var t → Exp t I → Stmt t
    Skip          : Stmt t
    _\\_          : Stmt t → Stmt t → Stmt t
    If_Then_Else_ : Exp t B → Stmt t → Stmt t → Stmt t
    While_Do_     : Exp t B → Stmt t → Stmt t
    Lock   : Stmt t
    Unlock : Stmt t
    LFence : Stmt t
    SFence : Stmt t


data Val2 : Set where
  ival : ℕ  → Val2
  bval : Bool → Val2

LockSt : Set
LockSt = Maybe Thr

GlobMem : Set
GlobMem = Glob → Val I

Cache : Set
Cache = List (Glob × Val I)

LocMem : Thr → Set
LocMem t = Loc t → Val I

record GlobCfg : Set where
  constructor 〈_/_〉
  field
    lockSt  : LockSt
    globMem : GlobMem

record LocCfg (t : Thr) : Set where
  constructor 〈_/_/_/_〉
  field
    residStmt  : Maybe (Stmt t)
    locMem     : LocMem t
    readCache  : Cache
    writeCache : Cache

record LocCfgExp (t : Thr) (y : Ty) : Set where
  constructor 〈_/_/_/_〉
  field
    residExp   : Exp t y
    locMem     : LocMem t
    readCache  : Cache
    writeCache : Cache


LocCfgs : Set
LocCfgs = (t : Thr) → LocCfg t

notblocked : LockSt → Thr → Set
notblocked nothing  t' = ⊤
notblocked (just t) t' = t ≡ t'

-- c₂ is a correctly dequeued c₁
postulate _⇒_ : Cache → Cache → Set
--c₁ ⇒ c₂ = {!!}
