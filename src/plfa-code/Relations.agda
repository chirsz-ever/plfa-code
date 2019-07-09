module plfa-code.Relations where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym; trans)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Data.Nat.Properties using (+-comm)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Function

data _≤_ : ℕ → ℕ → Set where
  z≤n : ∀ {n : ℕ}
      ---------
    → zero ≤ n

  s≤s : ∀ {m n : ℕ}
    → m ≤ n
      --------------
    → suc m ≤ suc n

infix 4 _≤_

_ : 2 ≤ 4
_ = s≤s (s≤s z≤n)

inv-s≤s : ∀ {m n : ℕ}
  → suc m ≤ suc n
     -------------
  → m ≤ n
inv-s≤s (s≤s m≤n) = m≤n

inv-z≤n : ∀ {m : ℕ}
  → m ≤ zero
    ---------
  → m ≡ zero
inv-z≤n z≤n = refl

≤-refl : ∀ {n : ℕ}
    ------
  → n ≤ n
≤-refl {zero} = z≤n
≤-refl {suc n} = s≤s ≤-refl

≤-trans : ∀ {m n p : ℕ}
  → m ≤ n
  → n ≤ p
    ------
  → m ≤ p
≤-trans z≤n _ = z≤n
≤-trans (s≤s m≤n) (s≤s n≤p) = s≤s (≤-trans m≤n n≤p)

≤-trans′ : ∀ (m n p : ℕ)
  → m ≤ n
  → n ≤ p
    ------
  → m ≤ p
≤-trans′ zero    _       _       z≤n       _          =  z≤n
≤-trans′ (suc m) (suc n) (suc p) (s≤s m≤n) (s≤s n≤p)  =  s≤s (≤-trans′ m n p m≤n n≤p)

≤-antisym : ∀ {m n : ℕ}
  → m ≤ n
  → n ≤ m
    -------
  → m ≡ n
≤-antisym z≤n z≤n = refl
≤-antisym (s≤s m≤n) (s≤s n≤m) = cong suc (≤-antisym m≤n n≤m)

-- when m is zero there is no instance for `n ≤ m`, the same as when n is zero

data Total (m n : ℕ) : Set where
  forward :
      m ≤ n
      ----------
    → Total m n

  flipped :
      n ≤ m
      ----------
    → Total m n


≤-total : ∀ (m n : ℕ) → Total m n
≤-total zero n = forward z≤n
≤-total (suc m) zero = flipped z≤n
≤-total (suc m) (suc n) with ≤-total m n
...                        | forward m≤n = forward (s≤s m≤n)
...                        | flipped n≤m = flipped (s≤s n≤m)

≤-total′ : ∀ (m n : ℕ) → Total m n
≤-total′ zero    n        =  forward z≤n
≤-total′ (suc m) zero     =  flipped z≤n
≤-total′ (suc m) (suc n)  =  helper (≤-total′ m n)
  where
  helper : Total m n → Total (suc m) (suc n)
  helper (forward m≤n)  =  forward (s≤s m≤n)
  helper (flipped n≤m)  =  flipped (s≤s n≤m)

+-monoʳ-≤ : ∀ (n p q : ℕ)
  → p ≤ q
    --------------
  → n + p ≤ n + q
+-monoʳ-≤ zero p q p≤q = p≤q
+-monoʳ-≤ (suc n) p q p≤q = s≤s (+-monoʳ-≤ n p q p≤q)

+-monoˡ-≤ : ∀ (m n p : ℕ)
  → m ≤ n
    --------------
  → m + p ≤ n + p
+-monoˡ-≤ m n p m≤n rewrite +-comm m p | +-comm n p = +-monoʳ-≤ p m n m≤n

+-mono-≤ : ∀ (m n p q : ℕ)
  → m ≤ n
  → p ≤ q
    --------------
  → m + p ≤ n + q
+-mono-≤ m n p q m≤n p≤q = ≤-trans (+-monoˡ-≤ m n p m≤n) (+-monoʳ-≤ n p q p≤q)

---------- practice ----------
*-mono-≤ : ∀ (m n p q : ℕ) → m ≤ n → p ≤ q → m * p ≤ n * q
*-mono-≤ zero n p q m≤n p≤q = z≤n
*-mono-≤ (suc m) (suc n) p q m≤n p≤q = +-mono-≤ p q (m * p) (n * q) p≤q (*-mono-≤ m n p q (inv-s≤s m≤n) p≤q)
------------------------------

infix 4 _<_

data _<_ : ℕ → ℕ → Set where
  z<s : ∀ {n : ℕ}
      -------------
    → zero < suc n

  s<s : ∀ {m n : ℕ}
    → m < n
      --------------
    → suc m < suc n

---------- practice ----------
inv-s<s : ∀ {m n : ℕ} → suc m < suc n → m < n
inv-s<s (s<s mLTn) = mLTn

<-trans : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans zero (suc n) (suc p) zLTsn snLTsp = z<s
<-trans (suc m) (suc n) (suc p) smLTsn snLTsp = s<s (<-trans m n p (inv-s<s smLTsn) (inv-s<s snLTsp))

data Trichotomy (m n : ℕ) : Set where
  less    : m < n → Trichotomy m n
  equal   : m ≡ n → Trichotomy m n
  greater : n < m → Trichotomy m n

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero    zero     = equal refl
<-trichotomy zero    (suc n)  = less z<s
<-trichotomy (suc m) zero     = greater z<s
<-trichotomy (suc m) (suc n) with <-trichotomy m n 
...                             | less    mLTn = less (s<s mLTn)
...                             | equal   refl = equal refl
...                             | greater nLTm = greater (s<s nLTm)

+-monoʳ-< : ∀ (n p q : ℕ) → p < q → n + p < n + q
+-monoʳ-< zero p q pLTq = pLTq
+-monoʳ-< (suc n) p q pLTq = s<s (+-monoʳ-< n p q pLTq)

+-monoˡ-< : ∀ (m n p : ℕ) → m < n → m + p < n + p
+-monoˡ-< m n p mLTn rewrite +-comm m p | +-comm n p = +-monoʳ-< p m n mLTn

+-mono-< : ∀ (m n p q : ℕ) → m < n → p < q → m + p < n + q
+-mono-< m n p q mLTn pLTq = <-trans (m + p) (n + p) (n + q) (+-monoˡ-< m n p mLTn) (+-monoʳ-< n p q pLTq)

≤-iff-< : ∀ (m n : ℕ) → suc m ≤ n → m < n
≤-iff-< zero    (suc n) _       = z<s
≤-iff-< (suc m) (suc n) ssm≤sn = s<s (≤-iff-< m n sm≤n)
  where
  sm≤n = inv-s≤s ssm≤sn

<-iff-≤ : ∀ (m n : ℕ) → m < n → suc m ≤ n
<-iff-≤ zero (suc n) mLTn = s≤s z≤n
<-iff-≤ (suc m) (suc n) smLTn = s≤s (<-iff-≤ m n (inv-s<s smLTn))

<→≤ : ∀ (n p : ℕ) → n < p → n ≤ p
<→≤ zero p nLTp = z≤n
<→≤ (suc n) (suc p) nLTp = s≤s (<→≤ n p (inv-s<s nLTp))

<-trans-revisited : ∀ (m n p : ℕ) → m < n → n < p → m < p
<-trans-revisited m n p mLTn nLTp = ≤-iff-< m p (inv-s≤s ssm≤sp)
  where ssm≤sp = s≤s (≤-trans (<-iff-≤ m n mLTn) (<→≤ n p nLTp))
------------------------------

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  zero :
      ---------
      even zero

  suc  : ∀ {n : ℕ}
    → odd n
      -------------
    → even (suc n)

data odd where

  suc   : ∀ {n : ℕ}
    → even n
      ------------
    → odd (suc n)

e+e≡e : ∀ {m n : ℕ}
  → even m
  → even n
    -------------
  → even (m + n)

o+e≡o : ∀ {m n : ℕ}
  → odd m
  → even n
    ------------
  → odd (m + n)

e+e≡e zero     en  =  en
e+e≡e (suc om) en  =  suc (o+e≡o om en)

o+e≡o (suc em) en  =  suc (e+e≡e em en)

---------- practice ----------
o+o≡e : ∀ {m n : ℕ} → odd m → odd n → even (m + n)
o+o≡e (suc zero)     on = suc on
o+o≡e (suc (suc ox)) on = suc (suc (o+o≡e ox on))

open import plfa-code.Induction using (Bin; nil; x0_; x1_; inc; from; to;
                                      +1≡suc; suc-from-inc; from-to-const)

data Can : Bin → Set
data One : Bin → Set

data One where
  one  : One (x1 nil)
  x0_ : ∀ {b : Bin} → One b → One(x0 b)
  x1_ : ∀ {b : Bin} → One b → One(x1 b)

data Can where
  zero     : Can (x0 nil)
  can-one  : ∀ {b : Bin} → One b → Can b

one-inc : ∀ {x : Bin} → One x → One (inc x)
one-inc one = x0 one
one-inc (x0 x) = x1 x
one-inc (x1 x) = x0 (one-inc x)

can-inc : ∀ {x : Bin} → Can x → Can (inc x)
can-inc zero        =  can-one one
can-inc (can-one x) =  can-one (one-inc x)

one-to-n : ∀ (n : ℕ) → One (to (suc n))
one-to-n zero = one
one-to-n (suc n) = one-inc (one-to-n n)

can-to-n : ∀ (n : ℕ) → Can (to n)
can-to-n zero = zero
can-to-n (suc n) = can-one (one-to-n n)


open Data.Nat.Properties using (+-identityʳ; +-suc)

l0 : ∀ (n) → to (suc n) ≡ inc (to n)
l0 zero    = refl
l0 (suc n) = refl

2n-eq-x0 : ∀ (n) → 1 ≤ n → to (n + n) ≡ x0 (to n)
2n-eq-x0 (suc zero) (s≤s z≤n) = refl
2n-eq-x0 (suc (suc n)) (s≤s z≤n) rewrite +-suc n (suc n)
                                       | 2n-eq-x0 (suc n) (s≤s z≤n) = refl

one-b-iff-1≤b : ∀ (b) → One b → 1 ≤ from b
one-b-iff-1≤b (x0 b) (x0 ob)
              rewrite +-identityʳ (from b)
              = +-mono-≤ 1 n 0 n (one-b-iff-1≤b b ob) z≤n
                where n = from b
one-b-iff-1≤b (x1 .nil) one     = s≤s z≤n
one-b-iff-1≤b (x1 b)    (x1 ob) = s≤s z≤n

one-tf-eq : ∀ {b} → One b → to (from b) ≡ b
one-tf-eq {_}    one    = refl
one-tf-eq {x0 b} (x0 x) =
  begin
    to (from (x0 b))
  ≡⟨⟩
    to (from b + (from b + zero))
  ≡⟨ cong (λ n → to (from b + n)) (+-identityʳ (from b)) ⟩
    to (from b + from b)
  ≡⟨ 2n-eq-x0 (from b) (one-b-iff-1≤b b x) ⟩
    x0 (to (from b))
  ≡⟨ cong x0_ (one-tf-eq x) ⟩
    x0 b
  ∎
one-tf-eq {x1 b} (x1 x) = 
  begin
    to (from (x1 b))
  ≡⟨⟩
    inc (to (from b + (from b + zero)))
  ≡⟨ cong (λ n → inc (to (from b + n))) (+-identityʳ (from b)) ⟩
    inc (to (from b + from b))
  ≡⟨ cong inc (2n-eq-x0 (from b) (one-b-iff-1≤b b x)) ⟩
    inc (x0 (to (from b)))
  ≡⟨⟩
    x1 (to (from b))
  ≡⟨ cong x1_ (one-tf-eq x) ⟩
    x1 b
  ∎

can-tf-eq : ∀ {x} → Can x → to (from x) ≡ x
can-tf-eq {_}  zero        = refl
can-tf-eq {b}  (can-one x) = one-tf-eq x

------------------------------
