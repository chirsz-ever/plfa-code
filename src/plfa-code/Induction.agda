module plfa-code.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Function

t1 : (3 + 4) + 5 ≡ 3 + (4 + 5)
t1 =
  begin
    (3 + 4) + 5
  ≡⟨⟩
    7 + 5
  ≡⟨⟩
    12
  ≡⟨⟩
    3 + 9
  ≡⟨⟩
    3 + (4 + 5)
  ∎

+-assoc : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)
+-assoc zero n p =
  begin
    (zero + n) + p
  ≡⟨⟩
    n + p
  ≡⟨⟩
    zero + (n + p)
  ∎
+-assoc (suc m) n p =
  begin
    (suc m + n) + p
  ≡⟨⟩
    suc (m + n) + p
  ≡⟨⟩
    suc ((m + n) + p)
  ≡⟨ cong suc (+-assoc m n p) ⟩
    suc (m + (n + p))
  ≡⟨⟩
    suc m + (n + p)
  ∎

+-identityʳ : ∀ (m : ℕ) → m + zero ≡ m
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎
+-identityʳ (suc m) =
  begin
    suc m + zero
  ≡⟨⟩
    suc (m + zero)
  ≡⟨ cong suc (+-identityʳ m)⟩
    suc m
  ∎

+-suc : ∀ (m n : ℕ) → m + suc n ≡ suc (m + n)
+-suc zero n =
  begin
    zero + suc n
  ≡⟨⟩
    suc n
  ≡⟨⟩
    suc (zero + n)
  ∎
+-suc (suc m) n =
  begin
    suc m + suc n
  ≡⟨⟩
    suc (m + suc n)
  ≡⟨ cong suc (+-suc m n) ⟩
    suc (suc (m + n))
  ≡⟨⟩
    suc (suc m + n)
  ∎

+-comm : ∀ (m n : ℕ) → m + n ≡ n + m
+-comm zero n =
  begin
    zero + n
  ≡⟨⟩
    n
  ≡⟨ sym (+-identityʳ n) ⟩
    n + zero
  ∎
+-comm (suc m) n =
  begin
    suc m + n
  ≡⟨⟩
    suc (m + n)
  ≡⟨ cong suc (+-comm m n) ⟩
    suc (n + m)
  ≡⟨ sym (+-suc n m) ⟩
    n + suc m
  ∎

+-rearrange : ∀ (m n p q : ℕ) → (m + n) + (p + q) ≡ m + (n + p) + q
+-rearrange m n p q =
  begin
    (m + n) + (p + q)
  ≡⟨ +-assoc m n (p + q) ⟩
    m + (n + (p + q))
  ≡⟨ cong (m +_) (sym (+-assoc n p q)) ⟩
    m + ((n + p) + q)
  ≡⟨ sym (+-assoc m (n + p) q) ⟩
    (m + (n + p)) + q
  ∎

+-assoc′ : ∀ (m n p : ℕ) → (m + n) + p ≡ m + (n + p)  
+-assoc′ zero n p = refl
+-assoc′ (suc m) n p rewrite +-assoc′ m n p = refl


-- practice

+-swap : ∀ (m n p : ℕ) → m + (n + p) ≡ n + (m + p)
+-swap m zero p = refl
+-swap m (suc n) p
  rewrite +-suc m (n + p)
  | sym (+-assoc m n p)
  | +-comm m n
  | +-assoc n m p = refl

*-distrib-+ : ∀ (m n p : ℕ) → (m + n) * p ≡ m * p + n * p
*-distrib-+ zero n p = refl
*-distrib-+ (suc m) n p rewrite *-distrib-+ m n p
                                | sym (+-assoc p (m * p) (n * p)) = refl

*-assoc : ∀ (m n p : ℕ) → (m * n) * p ≡ m * (n * p)
*-assoc zero n p = refl
*-assoc (suc m) n p rewrite *-distrib-+ n (m * n) p | *-assoc m n p = refl

*-zeroʳ : ∀ (n : ℕ) → n * zero ≡ zero
*-zeroʳ zero = refl
*-zeroʳ (suc n) rewrite *-zeroʳ n = refl

*-suc : ∀ (m n : ℕ) → m * suc n ≡ m * n + m
*-suc zero n = refl
*-suc (suc m) n =
  begin
    (suc m) * (suc n)
  ≡⟨⟩
    (suc n) + m * (suc n)
  ≡⟨ cong ((suc n) +_) (*-suc m n) ⟩
    suc n + (m * n + m)
  ≡⟨ +-swap (suc n) (m * n) m ⟩
    m * n + (suc n + m)
  ≡⟨ cong ((m * n) +_) (sym (+-suc n m)) ⟩
    m * n + (n + suc m)
  ≡⟨ sym (+-assoc (m * n) n (suc m)) ⟩
    m * n + n + suc m
  ≡⟨ cong (_+ (suc m)) (+-comm (m * n) n) ⟩
    (suc m) * n + (suc m)
  ∎

*-comm : ∀ (m n : ℕ) → m * n ≡ n * m
*-comm zero n rewrite *-zeroʳ n = refl
*-comm (suc m) n =
  begin
    suc m * n
  ≡⟨⟩
    n + m * n
  ≡⟨ +-comm n (m * n) ⟩
    m * n + n
  ≡⟨ cong (_+ n) (*-comm m n) ⟩
    n * m + n
  ≡⟨ sym (*-suc n m) ⟩
    n * suc m
  ∎

t2 : ∀ (n : ℕ) → zero ∸ n ≡ zero
t2 zero = refl
t2 (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite t2 n | t2 p | t2 (n + p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

---------- Bin ----------
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil = x1 nil
inc (x0 t) = x1 t
inc (x1 t) = x0 (inc t)

to   : ℕ → Bin
to 0   = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil      = 0
from (x0 t)   = (from t) * 2
from (x1 t)   = (from t) * 2 + 1
--------------------------------------

l1 : ∀ (n : ℕ) → n + 1 ≡ suc n
l1 zero = refl
l1 (suc n) rewrite l1 n = refl

t3 : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
t3 nil = refl
t3 (x0 x) rewrite l1 (from x * 2) = refl
t3 (x1 x) rewrite t3 x | sym (l1 (from x * 2)) = refl

-- t4 is ⊥ , because `to (from nil) ≡ x0 nil ≢ nil`
-- t4 : ∀ (x : Bin) → to (from x) ≡ x

t5 : ∀ (n : ℕ) → from (to n) ≡ n
t5 zero = refl
t5 (suc n) rewrite t3 (to n) | t5 n = refl
