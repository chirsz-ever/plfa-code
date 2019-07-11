module plfa-code.Negation where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_×_) renaming (_,_ to ⟨_,_⟩)
open import plfa-code.Isomorphism using (_≃_; extensionality)

¬_ : Set → Set
¬ A = A → ⊥

¬-elim : ∀ {A : Set}
  → ¬ A
  → A
    ---
  → ⊥
¬-elim ¬x x = ¬x x

infix 3 ¬_

¬¬-intro : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro x  =  λ ¬x → ¬x x

¬¬-intro′ : ∀ {A : Set}
  → A
    -----
  → ¬ ¬ A
¬¬-intro′ x ¬x = ¬x x

¬¬¬-elim : ∀ {A : Set}
  → ¬ ¬ ¬ A
    -------
  → ¬ A
¬¬¬-elim ¬¬¬x  =  λ x → ¬¬¬x (¬¬-intro x)

contraposition : ∀ {A B : Set}
  → (A → B)
    ------------
  → (¬ B → ¬ A)
contraposition f ¬y x = ¬y (f x)

_≢_ : ∀ {A : Set} → A → A → Set
x ≢ y  =  ¬ (x ≡ y)

_ : 1 ≢ 2
_ = λ ()

peano : ∀ {m : ℕ} → zero ≢ suc m
peano = λ ()

id : ⊥ → ⊥
id x = x

id′ : ⊥ → ⊥
id′ ()

id≡id′ : id ≡ id′
id≡id′ = extensionality (λ ())

assimilation : ∀ {A : Set} (¬x ¬x′ : ¬ A) → ¬x ≡ ¬x′
assimilation ¬x ¬x′ = extensionality (λ x → ⊥-elim (¬x′ x))

open Data.Nat using (_<_; _≤_; z≤n; s≤s)
open Relation.Binary.PropositionalEquality using (cong)
open import Function
open Data.Product using (proj₁; proj₂)

---------- practice ----------

<-irreflexive : ∀ {n : ℕ} → ¬ (n < n)
<-irreflexive {suc n} (s≤s n<n) = <-irreflexive n<n

data Trichotomy (m n : ℕ) : Set where
  less    : m < n → ¬ (n < m) → ¬ (m ≡ n) → Trichotomy m n
  greater : n < m → ¬ (m ≡ n) → ¬ (m < n) → Trichotomy m n
  equal   : m ≡ n → ¬ (m < n) → ¬ (n < m) → Trichotomy m n

inv-< : ∀ {m n} → suc m < suc n → m < n
inv-< (s≤s sm<sn) = sm<sn

inv-≡ : ∀ {m n} → suc m ≡ suc n → m ≡ n
inv-≡ refl = refl

<-trichotomy : ∀ (m n : ℕ) → Trichotomy m n
<-trichotomy zero    zero    = equal refl      (λ ()) (λ ())
<-trichotomy zero    (suc n) = less  (s≤s z≤n) (λ ()) (λ ())
<-trichotomy (suc m) zero    = greater (s≤s z≤n) (λ ()) (λ ())
<-trichotomy (suc m) (suc n) with <-trichotomy m n
... | less    m<n ¬n<m ¬m≡n = less       (s≤s m<n) (¬n<m ∘ inv-<) (¬m≡n ∘ inv-≡)
... | greater n<m ¬m≡n ¬m<n = greater    (s≤s n<m) (¬m≡n ∘ inv-≡) (¬m<n ∘ inv-<)
... | equal   m≡n ¬m<n ¬n<m = equal (cong suc m≡n) (¬m<n ∘ inv-<) (¬n<m ∘ inv-<)

⊎-dual-× : ∀ (A B) → ¬ (A ⊎ B) ≃ (¬ A) × (¬ B)
⊎-dual-× A B =
  record
  { to      = λ ¬-A⊎B → ⟨ (¬-A⊎B ∘ inj₁) , (¬-A⊎B ∘ inj₂) ⟩
  ; from    = λ{ ¬A×¬B (inj₁ a) → proj₁ ¬A×¬B a
               ; ¬A×¬B (inj₂ b) → proj₂ ¬A×¬B b
               }
  ; from∘to = λ{x → assimilation _ x}
  ; to∘from = λ{ ⟨ ¬a , ¬b ⟩ → refl}
  }

-- ¬ (A × B) ≃ (¬ A) ⊎ (¬ B) does not hold, but we could say:
⊎¬-implies-¬× : ∀ (A B) → (¬ A) ⊎ (¬ B) → ¬ (A × B)
⊎¬-implies-¬× A B (inj₁ ¬a) = λ ab → ¬a (proj₁ ab)
⊎¬-implies-¬× A B (inj₂ ¬b) = λ ab → ¬b (proj₂ ab)

------------------------------

em-irrefutable : ∀ {A : Set} → ¬ ¬ (A ⊎ ¬ A)
em-irrefutable k = k (inj₂ (λ x → k (inj₁ x)))

---------- practice ----------
-- to prove the implying relations among a group of
-- proposition P₀ P₁ P₂ ... Pₙ, we just need prove P₀ → P₁,
-- P₁ → P₂, ..., Pₙ₋₁ → Pₙ, Pₙ → P₀.

P₀ = ∀ {A : Set} → A ⊎ ¬ A
P₁ = ∀ {A : Set} → (¬ ¬ A → A)
P₂ = ∀ {A B : Set} → ((A → B) → A) → A
P₃ = ∀ {A B : Set} → (A → B) → ¬ A ⊎ B
P₄ = ∀ {A B : Set} → ¬ (¬ A × ¬ B) → A ⊎ B

P₀⇒P₁ : P₀ → P₁
P₀⇒P₁ p₀ {A} ¬¬a with p₀ {A} 
...                 | inj₁ a  = a
...                 | inj₂ ¬a = ⊥-elim (¬¬a ¬a)

P₁⇒P₂ : P₁ → P₂
P₁⇒P₂ p₁ x = p₁ $ λ ¬a → (¬a $ x $ p₁ ∘ const ∘ ¬a)

P₂⇒P₃ : P₂ → P₃
P₂⇒P₃ p₂ {A} {B} f = p₂ {¬ A ⊎ B} {⊥} (λ z → inj₁ (z ∘ inj₂ ∘ f))

--- the prove 'P₃⇒P₄'  below referenced https://github.com/googleson78/plfa

P₃⇒P₀ : P₃ → P₀
P₃⇒P₀ p₃ {A} with p₃ Function.id
...        | inj₁ ¬x = inj₂ ¬x
...        | inj₂  x = inj₁ x

P₁⇒P₄ : P₁ → P₄
P₁⇒P₄ p₁ {A} {B} ¬x = p₁ (λ ¬y → ¬x ⟨ ¬y ∘ inj₁ , ¬y ∘ inj₂ ⟩)

P₃⇒P₄ : P₃ → P₄
P₃⇒P₄ = P₁⇒P₄ ∘ P₀⇒P₁ ∘ P₃⇒P₀

P₄⇒P₀ : P₄ → P₀
P₄⇒P₀ p₄ {A} = p₄ {A} {¬ A} $ proj₂ ˢ proj₁

Stable : Set → Set
Stable A = ¬ ¬ A → A

¬⇒stable : ∀ {A : Set} → ¬ A → Stable (¬ A)
¬⇒stable ¬a = ¬¬¬-elim

×⇒stable : ∀ {A B : Set} → Stable A → Stable B → Stable (A × B)
×⇒stable a b = λ x → ⟨ (a $ λ z → x (z ∘ proj₁)) , (b $ λ z → x (z ∘ proj₂)) ⟩
