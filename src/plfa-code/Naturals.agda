module plfa-code.Naturals where

data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

{-# BUILTIN NATURAL ℕ #-}

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎)

_+_ : ℕ → ℕ → ℕ
zero + n = n
suc m + n = suc (m + n)

_ : 2 + 3 ≡ 5
_ = refl

_*_ : ℕ → ℕ → ℕ
zero  * n  =  zero
suc m * n  =  n + (m * n)

_^_ : ℕ → ℕ → ℕ
n ^ zero    = suc zero
n ^ (suc m) = n * (n ^ m)

_ : 3 ^ 4 ≡ 81
_ =
  begin
    3 ^ 4
  ≡⟨⟩
    3 * (3 ^ 3)
  ≡⟨⟩
    3 * (3 * (3 ^ 2))
  ≡⟨⟩
    3 * (3 * (3 * (3 ^ 1)))
  ≡⟨⟩
    3 * (3 * (3 * (3 * (3 ^ 0))))
  ≡⟨⟩
    3 * (3 * (3 * (3 * 1)))
  ≡⟨⟩
    81
  ∎

_∸_ : ℕ → ℕ → ℕ
m     ∸ zero   =  m
zero  ∸ suc n  =  zero
suc m ∸ suc n  =  m ∸ n

_ =
  begin
     3 ∸ 2
  ≡⟨⟩
     2 ∸ 1
  ≡⟨⟩
     1 ∸ 0
  ≡⟨⟩
     1
  ∎

_ =
  begin
     2 ∸ 3
  ≡⟨⟩
     1 ∸ 2
  ≡⟨⟩
     0 ∸ 1
  ≡⟨⟩
     0
  ∎

infixl 6 _+_ _∸_
infixl 7 _*_

data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 t) = x1 t
inc (x1 t) = x0 (inc t)

_ : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
_ = refl

_ : inc (x0 nil) ≡ x1 nil
_ = refl

_ : inc (x1 nil) ≡ x0 x1 nil
_ = refl

_ : inc (x0 x1 nil) ≡ x1 x1 nil
_ = refl

_ : inc (x1 x1 nil) ≡ x0 x0 x1 nil
_ = refl

to   : ℕ → Bin
to 0   = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil      = 0
from (x0 t)   = (from t) * 2
from (x1 t)   = (from t) * 2 + 1

_ : to 0 ≡ x0 nil
_ = refl

_ : to 1 ≡ x1 nil
_ = refl

_ : to 2 ≡ x0 x1 nil
_ = refl

_ : to 3 ≡ x1 x1 nil
_ = refl

_ : to 4 ≡ x0 x0 x1 nil
_ = refl

_ : 0 ≡ from (x0 nil)
_ = refl

_ : 1 ≡ from (x1 nil)
_ = refl

_ : 2 ≡ from (x0 x1 nil)
_ = refl

_ : 3 ≡ from (x1 x1 nil)
_ = refl

_ : 4 ≡ from (x0 x0 x1 nil)
_ = refl

