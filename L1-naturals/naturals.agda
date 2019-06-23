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

a : 2 + 3 ≡ 5
a = refl

_*_ : ℕ → ℕ → ℕ
zero  * n  =  zero
suc m * n  =  n + (m * n)

_^_ : ℕ → ℕ → ℕ
n ^ zero    = suc zero
n ^ (suc m) = n * (n ^ m)

b : 3 ^ 4 ≡ 81
b =
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

c =
  begin
     3 ∸ 2
  ≡⟨⟩
     2 ∸ 1
  ≡⟨⟩
     1 ∸ 0
  ≡⟨⟩
     1
  ∎

d =
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

d1 : inc (x1 x1 x0 x1 nil) ≡ x0 x0 x1 x1 nil
d1 = refl

d2 : inc (x0 nil) ≡ x1 nil
d2 = refl

d3 : inc (x1 nil) ≡ x0 x1 nil
d3 = refl

d4 : inc (x0 x1 nil) ≡ x1 x1 nil
d4 = refl

d5 : inc (x1 x1 nil) ≡ x0 x0 x1 nil
d5 = refl

to   : ℕ → Bin
to 0   = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil      = 0
from (x0 t)   = (from t) * 2
from (x1 t)   = (from t) * 2 + 1

e00 : to 0 ≡ x0 nil
e00 = refl

e01 : to 1 ≡ x1 nil
e01 = refl

e02 : to 2 ≡ x0 x1 nil
e02 = refl

e03 : to 3 ≡ x1 x1 nil
e03 = refl

e04 : to 4 ≡ x0 x0 x1 nil
e04 = refl

e10 : 0 ≡ from (x0 nil)
e10 = refl

e11 : 1 ≡ from (x1 nil)
e11 = refl

e12 : 2 ≡ from (x0 x1 nil)
e12 = refl

e13 : 3 ≡ from (x1 x1 nil)
e13 = refl

e14 : 4 ≡ from (x0 x0 x1 nil)
e14 = refl

