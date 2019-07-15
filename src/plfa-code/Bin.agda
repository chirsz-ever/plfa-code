module plfa-code.Bin where

-- I collect code about Bin there. other definitions I use the std-lib version

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; cong; sym)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _≡⟨_⟩_; _∎)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (+-comm; +-suc; +-mono-≤)

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

+1≡suc : ∀ {n : ℕ} → n + 1 ≡ suc n
+1≡suc {zero}   = refl
+1≡suc {suc n}  = cong suc +1≡suc

suc-from-inc : ∀ (x : Bin) → from (inc x) ≡ suc (from x)
suc-from-inc nil                                        = refl
suc-from-inc (x0 x) rewrite +1≡suc {from x * 2}         = refl
suc-from-inc (x1 x) rewrite suc-from-inc x
                          | +-suc (from x) (from x + 0) = refl

-- t4 is ⊥ , because `to (from nil) ≡ x0 nil ≢ nil`
-- t4 : ∀ (x : Bin) → to (from x) ≡ x

from-to-const : ∀ (n : ℕ) → from (to n) ≡ n
from-to-const zero                               =  refl
from-to-const (suc n) rewrite suc-from-inc (to n)
                            | from-to-const n    =  refl

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
              rewrite +-identityʳ (from b) = +-mono-≤ (one-b-iff-1≤b b ob) z≤n
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

open import Function.LeftInverse using (_↞_)

ℕ-embedding-Bin : ℕ ↞ Bin
ℕ-embedding-Bin =
  record
  { to              = record { _⟨$⟩_ = to   ; cong = cong to }
  ; from            = record { _⟨$⟩_ = from ; cong = cong from }
  ; left-inverse-of = from-to-const
  }

open import Function.Inverse using (_↔_)
open import Data.Product
  using (Σ; ∃; Σ-syntax; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)

one-assim : ∀ {b : Bin} → (x : One b) → (y : One b) → x ≡ y
one-assim one one = refl
one-assim (x0 x) (x0 y) = sym (cong x0_ (one-assim y x))
one-assim (x1 x) (x1 y) = sym (cong x1_ (one-assim y x))

can-assim : ∀ {b : Bin} → (x : Can b) → (y : Can b) → x ≡ y
can-assim zero zero = refl
can-assim zero (can-one (x0 ()))
can-assim (can-one (x0 ())) zero
can-assim (can-one one) (can-one one) = refl
can-assim (can-one (x0 x)) (can-one (x0 y)) = cong (can-one ∘ x0_) (one-assim x y)
can-assim (can-one (x1 x)) (can-one (x1 y)) = cong (can-one ∘ x1_) (one-assim x y)

∃-proj₁ : {A : Set} {B : A → Set} → ∃[ x ] B x → A
∃-proj₁ ⟨ x , _ ⟩ = x

∃≡ : ∀ {A : Set} {B : A → Set} (p₁ : ∃[ x ](B x)) (p₂ : ∃[ y ](B y))
  → ∃-proj₁ p₁ ≡ ∃-proj₁ p₂ → (∀ (x) → (b₁ : B x) → (b₂ : B x) → b₁ ≡ b₂)
  → p₁ ≡ p₂
∃≡ ⟨ x , bx ⟩ ⟨ .x , by ⟩ refl f = sym (cong (⟨_,_⟩ x) (f x by bx))

Bin-isomorphism : ℕ ↔ ∃[ x ](Can x)
Bin-isomorphism =
  record
  { to         = record { _⟨$⟩_ = to′; cong = cong to′}
  ; from       = record { _⟨$⟩_ = from′; cong = cong from′}
  ; inverse-of = record
                 { left-inverse-of = from-to-const
                 ; right-inverse-of = to∘from′
                 }
  }
  where
  to′ : ℕ → ∃[ x ](Can x)
  to′ n = ⟨ to n , can-to-n n ⟩
  from′ : ∃[ x ](Can x) → ℕ
  from′ ⟨ b , can-b ⟩ = from b
  to∘from′ : ∀ y → to′ (from′ y) ≡ y
  to∘from′ ⟨ b , can-b ⟩  = ∃≡ ⟨ to (from b) , can-to-n (from b) ⟩ ⟨ b , can-b ⟩ (can-tf-eq can-b) (λ x → can-assim {x})
