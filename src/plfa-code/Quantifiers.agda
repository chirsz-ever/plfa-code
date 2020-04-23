module plfa-code.Quantifiers where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_)
open import Relation.Nullary using (¬_)
open import Data.Product using (_×_; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import plfa-code.Isomorphism using (_≃_; extensionality)

∀-elim : ∀ {A : Set} {B : A → Set}
  → (L : ∀ (x : A) → B x)
  → (M : A)
    --------------------------
  → B M
∀-elim L M = L M

---------- practice ----------
∀-distrib-× : ∀ {A : Set} {B C : A → Set} →
  (∀ (x : A) → B x × C x) ≃ (∀ (x : A) → B x) × (∀ (x : A) → C x)
∀-distrib-× =
  record
  { to      = λ fₗ → ⟨ (λ a → proj₁ (fₗ a)) , (λ a → proj₂ (fₗ a)) ⟩
  ; from    = λ x a → ⟨ (proj₁ x a) , (proj₂ x a) ⟩
  ; from∘to = λ fₗ → refl
  ; to∘from = λ x  → refl
  }

⊎∀-implies-∀⊎ : ∀ {A : Set} {B C : A → Set} →
    (∀ (x : A) → B x) ⊎ (∀ (x : A) → C x)  →  ∀ (x : A) → B x ⊎ C x
⊎∀-implies-∀⊎ (inj₁ f₁) a = inj₁ (f₁ a)
⊎∀-implies-∀⊎ (inj₂ f₂) a = inj₂ (f₂ a)

-- the converse doesn't hold. If we construct a function
-- '∀ (x : A) → B x', we could build a '∀ (x : A) → B x ⊎ C x',
-- but '∀ (x : A) → C x' maybe doesn't hold.

data Tri : Set where
  aa : Tri
  bb : Tri
  cc : Tri

postulate
  ∀-extensionality :
    ∀ {A : Set} {B : A → Set} (f g : ∀ (x : A) → B x)
    → (∀ (x : A) → (f x ≡ g x))
    → f ≡ g

∀-× : {B : Tri → Set} → (∀ (x : Tri) → B x) ≃ (B aa × B bb × B cc)
∀-× {B} =
  record
  { to      = to′
  ; from    = from′
  ; from∘to = λ f → ∀-extensionality (from′ ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩) f
                                     λ{aa → refl; bb → refl; cc → refl}
  ; to∘from = λ xx → refl
  }
  where
  to′ : (∀ (x : Tri) → B x) → (B aa × B bb × B cc)
  to′ f = ⟨ f aa , ⟨ f bb , f cc ⟩ ⟩
  from′ : (B aa × B bb × B cc) → (∀ (x : Tri) → B x)
  from′ xx aa = proj₁ xx
  from′ xx bb = proj₁ (proj₂ xx)
  from′ xx cc = proj₂ (proj₂ xx)

-- every λ expression has different types , wtf
------------------------------

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → B) = Σ[ x ∈ A ] B

record Σ′ (A : Set) (B : A → Set) : Set where
  field
    proj₁′ : A
    proj₂′ : B proj₁′

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

∃-elim : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C)
  → ∃[ x ] B x
    ---------------
  → C
∃-elim f ⟨ x , y ⟩ = f x y

∀∃-currying : ∀ {A : Set} {B : A → Set} {C : Set}
  → (∀ x → B x → C) ≃ (∃[ x ] B x → C)
∀∃-currying =
  record
  { to      = λ{ f → λ{ ⟨ x , y ⟩ → f x y }}
  ; from    = λ{ g → λ{ x → λ{ y → g ⟨ x , y ⟩ }}}
  ; from∘to = λ f → refl
  ; to∘from = λ g → extensionality (λ{ ⟨ x , y ⟩ → refl})
  }

---------- practice ----------
∃-distrib-⊎ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x ⊎ C x) ≃ (∃[ x ] B x) ⊎ (∃[ x ] C x)
∃-distrib-⊎ =
  record
  { to      = λ{ ⟨ a , inj₁ b ⟩ → inj₁ ⟨ a , b ⟩
               ; ⟨ a , inj₂ c ⟩ → inj₂ ⟨ a , c ⟩
               }
  ; from    = λ{ (inj₁ ⟨ a , b ⟩) → ⟨ a , inj₁ b ⟩
               ; (inj₂ ⟨ a , c ⟩) → ⟨ a , inj₂ c ⟩
               }
  ; from∘to = λ{ ⟨ a , inj₁ b ⟩ → refl
               ; ⟨ a , inj₂ c ⟩ → refl
               }
  ; to∘from = λ{ (inj₁ ⟨ a , b ⟩) → refl
               ; (inj₂ ⟨ a , c ⟩) → refl
               }
  }

∃×-implies-×∃ : ∀ {A : Set} {B C : A → Set} →
  ∃[ x ] (B x × C x) → (∃[ x ] B x) × (∃[ x ] C x)
∃×-implies-×∃ ⟨ a , ⟨ b , c ⟩ ⟩ = ⟨ ⟨ a , b ⟩ , ⟨ a , c ⟩ ⟩

-- the converse doesn't hold, because the x in ∃[ x ] B x is maybe not
-- the same 'x' in ∃[ x ] C x

∃-⊎ : ∀ {B : Tri → Set} → ∃[ x ] B x ≃ B aa ⊎ B bb ⊎ B cc
∃-⊎ =
  record
  { to      = λ{ ⟨ aa , a ⟩ → inj₁ a
               ; ⟨ bb , b ⟩ → inj₂ (inj₁ b)
               ; ⟨ cc , c ⟩ → inj₂ (inj₂ c)
               }
  ; from    = λ{ (inj₁ a) → ⟨ aa , a ⟩
               ; (inj₂ (inj₁ b)) → ⟨ bb , b ⟩
               ; (inj₂ (inj₂ c)) → ⟨ cc , c ⟩
               }
  ; from∘to = λ{ ⟨ aa , a ⟩ → refl
               ; ⟨ bb , b ⟩ → refl
               ; ⟨ cc , c ⟩ → refl
               }
  ; to∘from = λ{ (inj₁ a) → refl
               ; (inj₂ (inj₁ b)) → refl
               ; (inj₂ (inj₂ c)) → refl
               }
  }

data even : ℕ → Set
data odd  : ℕ → Set

data even where

  even-zero : even zero

  even-suc : ∀ {n : ℕ}
    → odd n
      ------------
    → even (suc n)

data odd where
  odd-suc : ∀ {n : ℕ}
    → even n
      -----------
    → odd (suc n)

even-∃ : ∀ {n : ℕ} → even n → ∃[ m ] (    m * 2 ≡ n)
odd-∃  : ∀ {n : ℕ} →  odd n → ∃[ m ] (1 + m * 2 ≡ n)

even-∃ even-zero                       =  ⟨ zero  , refl ⟩
even-∃ (even-suc o) with odd-∃ o
...                    | ⟨ m , refl ⟩  =  ⟨ suc m , refl ⟩

odd-∃  (odd-suc e)  with even-∃ e
...                    | ⟨ m , refl ⟩  =  ⟨ m , refl ⟩

∃-even : ∀ {n : ℕ} → ∃[ m ] (    m * 2 ≡ n) → even n
∃-odd  : ∀ {n : ℕ} → ∃[ m ] (1 + m * 2 ≡ n) →  odd n

∃-even ⟨  zero , refl ⟩  =  even-zero
∃-even ⟨ suc m , refl ⟩  =  even-suc (∃-odd ⟨ m , refl ⟩)

∃-odd  ⟨     m , refl ⟩  =  odd-suc (∃-even ⟨ m , refl ⟩)

--------- practice ----------
open import Data.Nat.Properties using (+-identityʳ; +-suc; +-assoc)
open Eq using (cong; sym; trans)
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_)

open import plfa-code.Reasoning-legacy

∃-even′ : ∀ {n : ℕ} → ∃[ m ] (    2 * m ≡ n) → even n
∃-odd′  : ∀ {n : ℕ} → ∃[ m ] (2 * m + 1 ≡ n) →  odd n

dbl≡2* : ∀ n → n + n ≡ 2 * n
dbl≡2* n = cong (n +_) (sym (+-identityʳ n))

∃-even′ ⟨ zero , refl ⟩ = even-zero
∃-even′ ⟨ suc m , refl ⟩
  rewrite +-identityʳ m | +-suc m m | dbl≡2* m
                  = even-suc (odd-suc (∃-even′ ⟨ m , refl ⟩))

∃-odd′ ⟨ m , refl ⟩ rewrite +-suc (2 * m) 0
                          | +-identityʳ m
                          | +-identityʳ (m + m)
                          | dbl≡2* m           = odd-suc (∃-even′ ⟨ m , refl ⟩)
                          
-- it's more difficult far away ...

open Data.Nat using (_≤_; z≤n; s≤s)
open Data.Nat.Properties using (≤-pred)

∃+⇒≤ : ∀ (y z : ℕ) → ∃[ x ] (x + y ≡ z) → y ≤ z
∃+⇒≤ zero .(x + 0) ⟨ x , refl ⟩ = z≤n
∃+⇒≤ (suc y) .(x + suc y) ⟨ x , refl ⟩ rewrite +-suc x y
                                = s≤s (∃+⇒≤ y (x + y) ⟨ x , refl ⟩)

≤⇒∃+ : ∀ (y z : ℕ) → y ≤ z → ∃[ x ] (x + y ≡ z)
≤⇒∃+ zero z y≤z = ⟨ z , (+-identityʳ z) ⟩
≤⇒∃+ (suc y) (suc z) y≤z with ≤⇒∃+ y z (≤-pred y≤z)
...         | ⟨ x , x+y≡z ⟩ = ⟨ x , trans (+-suc x y) (cong suc x+y≡z) ⟩

-----------------------------

¬∃≃∀¬ : ∀ {A : Set} {B : A → Set}
  → (¬ ∃[ x ] B x) ≃ ∀ x → ¬ B x
¬∃≃∀¬ =
  record
    { to      = λ{ ¬∃xy x y → ¬∃xy ⟨ x , y ⟩ }
    ; from    = λ{ ∀¬xy ⟨ x , y ⟩ → ∀¬xy x y }
    ; from∘to = λ{ ¬∃xy → extensionality λ{ ⟨ x , y ⟩ → refl } }
    ; to∘from = λ{ ∀¬xy → refl }
    }

---------- practice ----------
∃¬-implies-¬∀ : ∀ {A : Set} {B : A → Set}
  → ∃[ x ] (¬ B x)
    --------------
  → ¬ (∀ x → B x)
∃¬-implies-¬∀ ⟨ a , ¬b ⟩ = λ a→b → ¬b (a→b a)
-- the converse doesn't hold. we couldn't get a instance
-- of A to construct ∃[ x ] (¬ B x)

open import plfa-code.Bin using (Bin; Can; One;
                                zero; can-one; x0_; x1_; nil; one;
                                from; to; can-to-n; can-tf-eq; from-to-const)
open Eq using (subst₂; cong₂)
open import Data.Empty using (⊥-elim)
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

Bin-isomorphism : ℕ ≃ ∃[ x ](Can x)
Bin-isomorphism =
  record
  { to      = to′
  ; from    = from′
  ; from∘to = from-to-const
  ; to∘from = to∘from′ 
  }
  where
  to′ : ℕ → ∃[ x ](Can x)
  to′ n = ⟨ to n , can-to-n n ⟩
  from′ : ∃[ x ](Can x) → ℕ
  from′ ⟨ b , can-b ⟩ = from b
  to∘from′ : ∀ y → to′ (from′ y) ≡ y
  to∘from′ ⟨ b , can-b ⟩  = ∃≡ ⟨ to (from b) , can-to-n (from b) ⟩ ⟨ b , can-b ⟩ (can-tf-eq can-b) (λ x → can-assim {x})
  
