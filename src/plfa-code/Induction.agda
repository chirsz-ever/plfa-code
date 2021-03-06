module plfa-code.Induction where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_)
open import Function

open import plfa-code.Reasoning-legacy 

_ : (3 + 4) + 5 ≡ 3 + (4 + 5)
_ =
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

z∸n≡z : ∀ (n : ℕ) → zero ∸ n ≡ zero
z∸n≡z zero = refl
z∸n≡z (suc n) = refl

∸-+-assoc : ∀ (m n p : ℕ) → m ∸ n ∸ p ≡ m ∸ (n + p)
∸-+-assoc zero n p rewrite z∸n≡z n | z∸n≡z p | z∸n≡z (n + p) = refl
∸-+-assoc (suc m) zero p = refl
∸-+-assoc (suc m) (suc n) p rewrite ∸-+-assoc m n p = refl

---------- Bin ----------
data Bin : Set where
  nil : Bin
  x0_ : Bin → Bin
  x1_ : Bin → Bin

inc : Bin → Bin
inc nil    = x1 nil
inc (x0 t) = x1 t
inc (x1 t) = x0 (inc t)

to : ℕ → Bin
to zero    = x0 nil
to (suc n) = inc (to n)

from : Bin → ℕ
from nil      = 0
from (x0 t)   = 2 * (from t)
from (x1 t)   = suc (2 * (from t))
--------------------------------------

+1≡suc : ∀ {n : ℕ} → n + 1 ≡ suc n
+1≡suc {zero}   = refl
+1≡suc {suc n}  = cong suc +1≡suc

suc-from-inc : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
suc-from-inc nil                                                        = refl
suc-from-inc (x0 x) rewrite +1≡suc {from x * 2}                         = refl
suc-from-inc (x1 x) rewrite suc-from-inc x | +-suc (from x) (from x + 0) = refl

-- t4 is ⊥ , because `to (from nil) ≡ x0 nil ≢ nil`
-- t4 : ∀ (x : Bin) → to (from x) ≡ x

from-to-const : ∀ (n : ℕ) → from (to n) ≡ n
from-to-const zero                                                  = refl
from-to-const (suc n) rewrite suc-from-inc (to n) | from-to-const n = refl
