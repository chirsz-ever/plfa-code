module plfa-code.Lists where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; sym; trans; cong)
open Eq.≡-Reasoning
open import Data.Bool using (Bool; true; false; T; _∧_; _∨_; not)
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _∸_; _≤_; s≤s; z≤n)
open import Data.Nat.Properties using
  (+-assoc; +-identityˡ; +-identityʳ; *-assoc; *-identityˡ; *-identityʳ)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Product using (_×_; ∃; ∃-syntax) renaming (_,_ to ⟨_,_⟩)
open import Function using (_∘_)
open import Level using (Level)
open import plfa-code.Isomorphism using (_≃_; _⇔_)

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

infixr 5 _∷_

_ : List ℕ
_ = 0 ∷ 1 ∷ 2 ∷ []

data List′ : Set → Set where
  []′  : ∀ {A : Set} → List′ A
  _∷′_ : ∀ {A : Set} → A → List′ A → List′ A

_ : List ℕ
_ = _∷_ {ℕ} 0 (_∷_ {ℕ} 1 (_∷_ {ℕ} 2 ([] {ℕ})))

{-# BUILTIN LIST List #-}

pattern [_] z = z ∷ []
pattern [_,_] y z = y ∷ z ∷ []
pattern [_,_,_] x y z = x ∷ y ∷ z ∷ []
pattern [_,_,_,_] w x y z = w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_] v w x y z = v ∷ w ∷ x ∷ y ∷ z ∷ []
pattern [_,_,_,_,_,_] u v w x y z = u ∷ v ∷ w ∷ x ∷ y ∷ z ∷ []

infixr 5 _++_

_++_ : ∀ {A : Set} → List A → List A → List A
[]       ++ ys  =  ys
(x ∷ xs) ++ ys  =  x ∷ (xs ++ ys)

_ : [ 0 , 1 , 2 ] ++ [ 3 , 4 ] ≡ [ 0 , 1 , 2 , 3 , 4 ]
_ = -- refl
  begin
    0 ∷ 1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ []
  ≡⟨⟩
    0 ∷ (1 ∷ 2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ (2 ∷ [] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ ([] ++ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ []
  ∎

++-assoc : ∀ {A : Set} (xs ys zs : List A)
  → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc [] ys zs = -- refl
  begin
    ([] ++ ys) ++ zs
  ≡⟨⟩
    ys ++ zs
  ≡⟨⟩
    [] ++ (ys ++ zs)
  ∎
++-assoc (x ∷ xs) ys zs = -- cong (_∷_ x) (++-assoc xs ys zs)
  begin
    (x ∷ xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ (xs ++ ys) ++ zs
  ≡⟨⟩
    x ∷ ((xs ++ ys) ++ zs)
  ≡⟨ cong (x ∷_) (++-assoc xs ys zs) ⟩
    x ∷ (xs ++ (ys ++ zs))
  ≡⟨⟩
    x ∷ xs ++ (ys ++ zs)
  ∎

++-identityˡ : ∀ {A : Set} (xs : List A) → [] ++ xs ≡ xs
++-identityˡ xs = -- refl
  begin
    [] ++ xs
  ≡⟨⟩
    xs
  ∎

++-identityʳ : ∀ {A : Set} (xs : List A) → xs ++ [] ≡ xs
++-identityʳ [] = -- refl
  begin
    [] ++ []
  ≡⟨⟩
    []
  ∎
++-identityʳ (x ∷ xs) = -- cong (_∷_ x) (++-identityʳ xs)
  begin
   (x ∷ xs) ++ []
  ≡⟨⟩
    x ∷ (xs ++ [])
  ≡⟨ cong (x ∷_) (++-identityʳ xs) ⟩
   x ∷ xs
  ∎

length : ∀ {A : Set} → List A → ℕ
length []       = zero
length (x ∷ xs) = suc (length xs)

_ : length [ 0 , 1 , 2 ] ≡ 3
_ = -- refl
  begin
    length (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc (length (1 ∷ 2 ∷ []))
  ≡⟨⟩
    suc (suc (length (2 ∷ [])))
  ≡⟨⟩
    suc (suc (suc (length {ℕ} [])))
  ≡⟨⟩
    suc (suc (suc zero))
  ∎

length-++ : ∀ {A : Set} (xs ys : List A)
  → length (xs ++ ys) ≡ length xs + length ys
length-++ {A} [] ys = -- refl
  begin
    length ([] ++ ys)
  ≡⟨⟩
    length ys
  ≡⟨⟩
    length {A} [] + length ys
  ∎
length-++ {A} (x ∷ xs) ys = -- cong suc (length-++ xs ys)
  begin
    length ((x ∷ xs) ++ ys)
  ≡⟨⟩
    suc (length (xs ++ ys))
  ≡⟨ cong suc (length-++ xs ys) ⟩
    suc (length xs + length ys)
  ≡⟨⟩
    length (x ∷ xs) + length ys
  ∎

reverse : ∀ {A : Set} → List A → List A
reverse [] = []
reverse (x ∷ xs) = reverse xs ++ [ x ]

_ : reverse [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    reverse (1 ∷ 2 ∷ []) ++ [ 0 ]
  ≡⟨⟩
    (reverse (2 ∷ []) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    ((reverse [] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ [ 2 ]) ++ [ 1 ]) ++ [ 0 ]
  ≡⟨⟩
    (([] ++ 2 ∷ []) ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ [] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ ([] ++ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    (2 ∷ 1 ∷ []) ++ 0 ∷ []
  ≡⟨⟩
    2 ∷ (1 ∷ [] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ ([] ++ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ≡⟨⟩
    [ 2 , 1 , 0 ]
  ∎

---------- practice ----------
reverse-++-commute : ∀ {A : Set} {xs ys : List A}
  → reverse (xs ++ ys) ≡ reverse ys ++ reverse xs
reverse-++-commute {_} {[]} {[]} = refl
reverse-++-commute {_} {[]} {y ∷ ys} = sym (++-identityʳ (reverse ys ++ [ y ]))
reverse-++-commute {_} {x ∷ xs} {ys} = 
  begin
    reverse ((x ∷ xs) ++ ys)
  ≡⟨⟩
    reverse (x ∷ (xs ++ ys))
  ≡⟨⟩
    reverse (xs ++ ys) ++ [ x ]
  ≡⟨ cong (_++ [ x ]) (reverse-++-commute {_} {xs} {ys}) ⟩
    (reverse ys ++ reverse xs) ++ [ x ]
  ≡⟨ ++-assoc (reverse ys) (reverse xs) [ x ] ⟩
    reverse ys ++ reverse xs ++ [ x ]
  ≡⟨ cong (reverse ys ++_) (sym refl) ⟩
    reverse ys ++ reverse ([ x ] ++ xs)
  ≡⟨⟩
    reverse ys ++ reverse (x ∷ xs)
  ∎

reverse-involutive : ∀ {A : Set} {xs : List A}
  → reverse (reverse xs) ≡ xs
reverse-involutive {_} {[]} = refl
reverse-involutive {_} {x ∷ xs} =
  begin
    reverse (reverse (x ∷ xs))
  ≡⟨⟩
    reverse (reverse xs ++ [ x ])
  ≡⟨ reverse-++-commute {_} {reverse xs} {[ x ]} ⟩
    reverse [ x ] ++ reverse (reverse xs)
  ≡⟨ cong (reverse [ x ] ++_) reverse-involutive ⟩
    [ x ] ++ xs
  ≡⟨⟩
    x ∷ xs
  ∎

------------------------------

shunt : ∀ {A : Set} → List A → List A → List A
shunt [] ys = ys
shunt (x ∷ xs) ys = shunt xs (x ∷ ys)

shunt-reverse : ∀ {A : Set} (xs ys : List A)
  → shunt xs ys ≡ (reverse xs) ++ ys
shunt-reverse [] ys = -- refl
  begin
    shunt [] ys
  ≡⟨⟩
    reverse [] ++ ys
  ∎
shunt-reverse (x ∷ xs) ys =
  begin
    shunt (x ∷ xs) ys
  ≡⟨⟩
    shunt xs (x ∷ ys)
  ≡⟨ shunt-reverse xs (x ∷ ys) ⟩
    reverse xs ++ (x ∷ ys)
  ≡⟨⟩
    reverse xs ++ ([ x ] ++ ys)
  ≡⟨ sym (++-assoc (reverse xs) [ x ] ys) ⟩
    (reverse xs ++ [ x ]) ++ ys
  ≡⟨⟩
    reverse (x ∷ xs) ++ ys
  ∎

reverse′ : ∀ {A : Set} → List A → List A
reverse′ xs = shunt xs []

reverses : ∀ {A : Set} (xs : List A)
  → reverse′ xs ≡ reverse xs
reverses xs =
  begin
    reverse′ xs
  ≡⟨⟩
    shunt xs []
  ≡⟨ shunt-reverse xs [] ⟩
    reverse xs ++ []
  ≡⟨ ++-identityʳ (reverse xs) ⟩
    reverse xs
  ∎

_ : reverse′ [ 0 , 1 , 2 ] ≡ [ 2 , 1 , 0 ]
_ =
  begin
    reverse′ (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    shunt (0 ∷ 1 ∷ 2 ∷ []) []
  ≡⟨⟩
    shunt (1 ∷ 2 ∷ []) (0 ∷ [])
  ≡⟨⟩
    shunt (2 ∷ []) (1 ∷ 0 ∷ [])
  ≡⟨⟩
    shunt [] (2 ∷ 1 ∷ 0 ∷ [])
  ≡⟨⟩
    2 ∷ 1 ∷ 0 ∷ []
  ∎

map : ∀ {A B : Set} → (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

_ : map suc [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    map suc (0 ∷ 1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ map suc (1 ∷ 2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ map suc (2 ∷ [])
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ map suc []
  ≡⟨⟩
    suc 0 ∷ suc 1 ∷ suc 2 ∷ []
  ≡⟨⟩
    1 ∷ 2 ∷ 3 ∷ []
  ∎

sucs : List ℕ → List ℕ
sucs = map suc

_ : sucs [ 0 , 1 , 2 ] ≡ [ 1 , 2 , 3 ]
_ =
  begin
    sucs [ 0 , 1 , 2 ]
  ≡⟨⟩
    map suc [ 0 , 1 , 2 ]
  ≡⟨⟩
    [ 1 , 2 , 3 ]
  ∎
---------- practice ----------
open plfa-code.Isomorphism using (extensionality)

map-compose : ∀ {A B C : Set} {f : A → B} {g : B → C}
  → map (g ∘ f) ≡ map g ∘ map f
map-compose {A} {B} {C} {f} {g} = extensionality hf
  where
  hf : (xs : List A) → map (g ∘ f) xs ≡ map g (map f xs)
  hf [] = refl
  hf (x ∷ xs) = cong ((g (f x)) ∷_) (hf xs)

map-++-commute : ∀ {A B : Set} {f : A → B} {xs ys : List A}
  →  map f (xs ++ ys) ≡ map f xs ++ map f ys
map-++-commute {A} {B} {f} {[]} {ys} = refl
map-++-commute {A} {B} {f} {x ∷ xs} {ys} =
  cong ((f x) ∷_) (map-++-commute {_} {_} {f} {xs} {ys})

data Tree (A B : Set) : Set where
  leaf : A → Tree A B
  node : Tree A B → B → Tree A B → Tree A B

map-Tree : ∀ {A B C D : Set}
  → (A → C) → (B → D) → Tree A B → Tree C D
map-Tree f g (leaf a) = leaf (f a)
map-Tree f g (node tree b tree₁) = node (map-Tree f g tree) (g b) (map-Tree f g tree₁)

------------------------------

foldr : ∀ {A B : Set} → (A → B → B) → B → List A → B
foldr _⊗_ e       []  =  e
foldr _⊗_ e (x ∷ xs)  =  x ⊗ (foldr _⊗_ e xs)

_ : foldr _+_ 0 [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    foldr _+_ 0 (1 ∷ 2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + foldr _+_ 0 (2 ∷ 3 ∷ 4 ∷ [])
  ≡⟨⟩
    1 + (2 + foldr _+_ 0 (3 ∷ 4 ∷ []))
  ≡⟨⟩
    1 + (2 + (3 + foldr _+_ 0 (4 ∷ [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + foldr _+_ 0 [])))
  ≡⟨⟩
    1 + (2 + (3 + (4 + 0)))
  ∎

sum : List ℕ → ℕ
sum = foldr _+_ 0

_ : sum [ 1 , 2 , 3 , 4 ] ≡ 10
_ =
  begin
    sum [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    foldr _+_ 0 [ 1 , 2 , 3 , 4 ]
  ≡⟨⟩
    10
  ∎

---------- practice ----------
product : List ℕ → ℕ
product = foldr _*_ 1

_ : product [ 1 , 2 , 3 , 4 ] ≡ 24
_ = refl

foldr-++ : ∀ {A B : Set} (_⊗_ : A → B → B) (e : B) (xs ys : List A) →
  foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ (foldr _⊗_ e ys) xs
foldr-++ _⊗_ e []       ys = refl
foldr-++ _⊗_ e (x ∷ xs) ys = cong (x ⊗_) (foldr-++ _⊗_ e xs ys)

map-is-foldr : ∀ {A B : Set} {f : A → B} →
  map f ≡ foldr (λ x xs → f x ∷ xs) []
map-is-foldr {A} {_} {f} = extensionality hf
  where
  hf : (l : List A) → map f l ≡ foldr (λ x xs → f x ∷ xs) [] l
  hf [] = refl
  hf (x ∷ xs) = cong (f x ∷_) (hf xs)
  
fold-Tree : ∀ {A B C : Set}
  → (A → C) → (C → B → C → C) → Tree A B → C
fold-Tree f g (leaf a)            = f a
fold-Tree f g (node tree b tree₁) = g (fold-Tree f g tree) b (fold-Tree f g tree₁)

downFrom : ℕ → List ℕ
downFrom zero     =  []
downFrom (suc n)  =  n ∷ downFrom n

_ : downFrom 3 ≡ [ 2 , 1 , 0 ]
_ = refl

open Data.Nat.Properties using
  (*-distribʳ-+; *-distribʳ-∸; m∸n+n≡m; m≤m+n;
   +-comm; *-comm; +-identityʳ; *-identityˡ)
open Eq using (cong₂)

2n≡n+n : ∀ n → 2 * n ≡ n + n
2n≡n+n zero = refl
2n≡n+n (suc n) = cong (λ x → suc (n + suc x)) (+-identityʳ n)

n≤n*n : ∀ n → n ≤ n * n
n≤n*n zero    = z≤n
n≤n*n (suc n) = s≤s (m≤m+n n (n * suc n))

sum-downFrom : ∀ (n : ℕ)
  → sum (downFrom n) * 2 ≡ n * (n ∸ 1)
sum-downFrom zero    = refl
sum-downFrom (suc n) =
  begin
    sum (downFrom (suc n)) * 2
  ≡⟨⟩
    (n + sum (downFrom n)) * 2
  ≡⟨ *-distribʳ-+ 2 n (sum (downFrom n)) ⟩
    n * 2 + sum (downFrom n) * 2
  ≡⟨ cong (n * 2 +_) (sum-downFrom n) ⟩
    n * 2 + n * (n ∸ 1)
  ≡⟨ cong₂ _+_ (*-comm n 2) (*-comm n (n ∸ 1)) ⟩
    2 * n + (n ∸ 1) * n
  ≡⟨ cong (2 * n +_) (*-distribʳ-∸ n n 1) ⟩
    2 * n + (n * n ∸ 1 * n)
  ≡⟨ cong₂ (λ a b → a + (n * n ∸ b)) (2n≡n+n n) (*-identityˡ n) ⟩
    n + n + (n * n ∸ n)
  ≡⟨ +-comm (n + n) (n * n ∸ n) ⟩
    n * n ∸ n + (n + n)
  ≡⟨ sym (+-assoc (n * n ∸ n) n n) ⟩
    n * n ∸ n + n + n
  ≡⟨ cong (_+ n) (m∸n+n≡m (n≤n*n n)) ⟩
    n * n + n
  ≡⟨ +-comm (n * n) n ⟩
    n + n * n
  ≡⟨⟩
    (suc n) * (suc n ∸ 1)
  ∎

------------------------------

record IsMonoid {A : Set} (_⊗_ : A → A → A) (e : A) : Set where
  field
    assoc : ∀ (x y z : A) → (x ⊗ y) ⊗ z ≡ x ⊗ (y ⊗ z)
    identityˡ : ∀ (x : A) → e ⊗ x ≡ x
    identityʳ : ∀ (x : A) → x ⊗ e ≡ x

open IsMonoid

+-monoid : IsMonoid _+_ 0
+-monoid =
  record
    { assoc = +-assoc
    ; identityˡ = +-identityˡ 
    ; identityʳ = +-identityʳ
    }

*-monoid : IsMonoid _*_ 1
*-monoid =
  record
    { assoc = *-assoc
    ; identityˡ = *-identityˡ
    ; identityʳ = *-identityʳ
    }

++-monoid : ∀ {A : Set} → IsMonoid {List A} _++_ []
++-monoid =
  record
    { assoc = ++-assoc
    ; identityˡ = ++-identityˡ
    ; identityʳ = ++-identityʳ
    }

foldr-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldr _⊗_ y xs ≡ foldr _⊗_ e xs ⊗ y
foldr-monoid _⊗_ e ⊗-monoid [] y = -- sym (identityˡ ⊗-monoid y)
  begin
    foldr _⊗_ y []
  ≡⟨⟩
    y
  ≡⟨ sym (identityˡ ⊗-monoid y) ⟩
    (e ⊗ y)
  ≡⟨⟩
    foldr _⊗_ e [] ⊗ y
  ∎
foldr-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldr _⊗_ y (x ∷ xs)
  ≡⟨⟩
    x ⊗ (foldr _⊗_ y xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid _⊗_ e ⊗-monoid xs y) ⟩
    x ⊗ ((foldr _⊗_ e xs) ⊗ y)
  ≡⟨ sym (assoc ⊗-monoid x (foldr _⊗_ e xs) y) ⟩
    (x ⊗ (foldr _⊗_ e xs)) ⊗ y
  ∎

foldr-monoid-++ : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs ys : List A) → foldr _⊗_ e (xs ++ ys) ≡ foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
foldr-monoid-++ _⊗_ e monoid-⊗ xs ys =
  begin
    foldr _⊗_ e (xs ++ ys)
  ≡⟨ foldr-++ _⊗_ e xs ys ⟩
    foldr _⊗_ (foldr _⊗_ e ys) xs
  ≡⟨ foldr-monoid _⊗_ e monoid-⊗ xs (foldr _⊗_ e ys) ⟩
    foldr _⊗_ e xs ⊗ foldr _⊗_ e ys
  ∎

---------- practice ----------
foldl : ∀ {A B : Set} → (B → A → B) → B → List A → B
foldl _⊗_ e       []  =  e
foldl _⊗_ e (x ∷ xs)  =  foldl _⊗_ (e ⊗ x) xs

foldl-monoid : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) (y : A) → foldl _⊗_ y xs ≡ y ⊗ foldl _⊗_ e xs
foldl-monoid _⊗_ e ⊗-monoid []       y = sym (identityʳ ⊗-monoid y)
foldl-monoid _⊗_ e ⊗-monoid (x ∷ xs) y =
  begin
    foldl _⊗_ y (x ∷ xs)
  ≡⟨⟩
    foldl _⊗_ (y ⊗ x) xs
  ≡⟨ foldl-monoid _⊗_ e ⊗-monoid xs (y ⊗ x) ⟩
    (y ⊗ x) ⊗ (foldl _⊗_ e xs)
  ≡⟨ assoc ⊗-monoid y x (foldl _⊗_ e xs) ⟩
    y ⊗ (x ⊗ foldl _⊗_ e xs)
  ≡⟨ sym (cong (y ⊗_) (foldl-monoid _⊗_ e ⊗-monoid xs x)) ⟩
    y ⊗ (foldl _⊗_ x xs)
  ≡⟨ sym (cong (λ z → y ⊗ foldl _⊗_ z xs) (identityˡ ⊗-monoid x)) ⟩
    y ⊗ (foldl _⊗_ (e ⊗ x) xs)
  ≡⟨⟩
    y ⊗ foldl _⊗_ e (x ∷ xs)
  ∎

foldr-monoid-foldl : ∀ {A : Set} (_⊗_ : A → A → A) (e : A) → IsMonoid _⊗_ e →
  ∀ (xs : List A) → foldr _⊗_ e xs ≡ foldl _⊗_ e xs
foldr-monoid-foldl _⊗_ e ⊗-monoid []       = refl
foldr-monoid-foldl _⊗_ e ⊗-monoid (x ∷ xs) =
  begin
    foldr _⊗_ e (x ∷ xs)
  ≡⟨⟩
    (x ⊗ foldr _⊗_ e xs)
  ≡⟨ cong (x ⊗_) (foldr-monoid-foldl _⊗_ e ⊗-monoid xs) ⟩
    (x ⊗ foldl _⊗_ e xs)
  ≡⟨ sym (foldl-monoid _⊗_ e ⊗-monoid xs x) ⟩
    foldl _⊗_ x xs
  ≡⟨ cong (λ a → foldl _⊗_ a xs) (sym (identityˡ ⊗-monoid x)) ⟩
    foldl _⊗_ (e ⊗ x) xs
  ≡⟨⟩
    foldl _⊗_ e (x ∷ xs)
  ∎

------------------------------

data All {A : Set} (P : A → Set) : List A → Set where
  []  : All P []
  _∷_ : ∀ {x : A} {xs : List A} → P x → All P xs → All P (x ∷ xs)

_ : All (_≤ 2) [ 0 , 1 , 2 ]
_ = z≤n ∷ s≤s z≤n ∷ s≤s (s≤s z≤n) ∷ []

data Any {A : Set} (P : A → Set) : List A → Set where
  here  : ∀ {x : A} {xs : List A} → P x → Any P (x ∷ xs)
  there : ∀ {x : A} {xs : List A} → Any P xs → Any P (x ∷ xs)

_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = here refl

_ : 0 ∈ [ 0 , 1 , 0 , 2 ]
_ = there (there (here refl))

not-in : 3 ∉ [ 0 , 0 , 0 , 2 ]
not-in (here ())
not-in (there (here ()))
not-in (there (there (here ())))
not-in (there (there (there (here ()))))
not-in (there (there (there (there ()))))

All-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ⇔ (All P xs × All P ys)
All-++-⇔ xs ys =
  record
    { to   = to xs ys
    ; from = from xs ys
    }
  where


  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to [] ys Pys = ⟨ [] , Pys ⟩
  to (x ∷ xs) ys (Px ∷ Pxs++ys) with to xs ys Pxs++ys
  ... | ⟨ Pxs , Pys ⟩ = ⟨ Px ∷ Pxs , Pys ⟩

  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from [] ys ⟨ [] , Pys ⟩ = Pys
  from (x ∷ xs) ys ⟨ Px ∷ Pxs , Pys ⟩ = Px ∷ (from xs ys ⟨ Pxs , Pys ⟩)

---------- practice ----------
open import Data.Sum using (_⊎_; inj₁; inj₂)
open Data.Product using (proj₁; proj₂)
open import Data.Empty using (⊥-elim)

Any-++-⇔ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  Any P (xs ++ ys) ⇔ (Any P xs ⊎ Any P ys)
Any-++-⇔ xs ys =
  record
  { to   = to xs ys
  ; from = from xs ys
  }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P (xs ++ ys) → Any P xs ⊎ Any P ys
  to []       ys Pys = inj₂ Pys
  to (x ∷ xs) ys (here Px)       = inj₁ (here Px)
  to (x ∷ xs) ys (there ∃Pxs++ys) with to xs ys ∃Pxs++ys
  ...                                | inj₁ ∃Pxs = inj₁ (there ∃Pxs)
  ...                                | inj₂ ∃Pys = inj₂ ∃Pys
  from : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    Any P xs ⊎ Any P ys → Any P (xs ++ ys)
  from [] ys (inj₂ ∃Pys) = ∃Pys
  from (x ∷ xs) ys (inj₁ (here Px))    = here Px
  from (x ∷ xs) ys (inj₁ (there ∃Pxs)) = there (from xs ys (inj₁ ∃Pxs))
  from (x ∷ xs) ys (inj₂ ∃Pys)         = there (from xs ys (inj₂ ∃Pys))

All-++-≃ : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
  All P (xs ++ ys) ≃ (All P xs × All P ys)
All-++-≃ {A} {P} xs ys =
  record
  { to      = to      xs ys
  ; from    = from    xs ys
  ; from∘to = from∘to xs ys
  ; to∘from = to∘from xs ys
  }
  where
  to : ∀ {A : Set} {P : A → Set} (xs ys : List A) →
    All P (xs ++ ys) → (All P xs × All P ys)
  to xs ys = _⇔_.to (All-++-⇔ xs ys)
  
  from : ∀ { A : Set} {P : A → Set} (xs ys : List A) →
    All P xs × All P ys → All P (xs ++ ys)
  from xs ys = _⇔_.from (All-++-⇔ xs ys)

  from∘to : ∀ (xs ys : List A) → (x : All P (xs ++ ys)) → from xs ys (to xs ys x) ≡ x
  from∘to [] ys x = refl
  from∘to (x ∷ xs) ys (Px ∷ ∀Pxs++ys) = -- cong (Px ∷_) (from∘to xs ys ∀Pxs++ys)
    begin
      from (x ∷ xs) ys (to (x ∷ xs) ys (Px ∷ ∀Pxs++ys))
    ≡⟨⟩
      from (x ∷ xs) ys ⟨ Px ∷ proj₁ (to xs ys ∀Pxs++ys) , proj₂ (to xs ys ∀Pxs++ys) ⟩
    ≡⟨⟩
      Px ∷ from xs ys ⟨ proj₁ (to xs ys ∀Pxs++ys) , proj₂ (to xs ys ∀Pxs++ys) ⟩
    ≡⟨⟩
      Px ∷ from xs ys (to xs ys ∀Pxs++ys)
    ≡⟨ cong (Px ∷_) (from∘to xs ys ∀Pxs++ys) ⟩
      Px ∷ ∀Pxs++ys
    ∎

  to∘from : ∀ (xs ys : List A)
    → (x : All P xs × All P ys)
    → to xs ys (from xs ys x) ≡ x
  to∘from [] ys ⟨ [] , ∀Pys ⟩ = refl
  to∘from (x ∷ xs) ys ⟨ Px ∷ ∀Pxs , ∀Pys ⟩ =
  --  cong (λ k → ⟨ Px ∷ (proj₁ k) , proj₂ k ⟩) (to∘from xs ys ⟨ ∀Pxs , ∀Pys ⟩)
    begin
      to (x ∷ xs) ys (from (x ∷ xs) ys ⟨ Px ∷ ∀Pxs , ∀Pys ⟩)
    ≡⟨⟩
      to (x ∷ xs) ys (Px ∷ (from xs ys ⟨ ∀Pxs , ∀Pys ⟩))
    ≡⟨⟩
      ⟨ Px ∷ (proj₁ (to xs ys (from xs ys ⟨ ∀Pxs , ∀Pys ⟩))) , (proj₂ (to xs ys (from xs ys ⟨ ∀Pxs , ∀Pys ⟩))) ⟩
    ≡⟨ cong (λ k → ⟨ Px ∷ (proj₁ k) , proj₂ k ⟩) (to∘from xs ys ⟨ ∀Pxs , ∀Pys ⟩) ⟩
      ⟨ Px ∷ (proj₁ ⟨ ∀Pxs , ∀Pys ⟩) , (proj₂ ⟨ ∀Pxs , ∀Pys ⟩) ⟩
    ≡⟨⟩
      ⟨ Px ∷ ∀Pxs , ∀Pys ⟩
    ∎

_∘′_ : ∀ {ℓ₁ ℓ₂ ℓ₃ : Level} {A : Set ℓ₁} {B : Set ℓ₂} {C : Set ℓ₃}
  → (B → C) → (A → B) → A → C
(g ∘′ f) x  =  g (f x)


¬Any≃All¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
  → (¬_ ∘′ Any P) xs ≃ All (¬_ ∘′ P) xs
¬Any≃All¬ P xs = 
  record
  { to      = to xs
  ; from    = from xs
  ; from∘to = from∘to xs
  ; to∘from = to∘from xs
  }
  where
  to : {A : Set} {P : A → Set} (xs : List A) →
    (¬_ ∘′ Any P) xs → All (¬_ ∘′ P) xs
  to []       ¬Any = []
  to (x ∷ xs) ¬Any = (λ Px → ¬Any (here Px)) ∷ to xs (λ Pxs → ¬Any (there Pxs))
  from : {A : Set} {P : A → Set} (xs : List A) →
    All (¬_ ∘′ P) xs → (¬_ ∘′ Any P) xs
  from (x ∷ xs) (¬Px ∷ All¬) (here Px) = ¬Px Px
  from (x ∷ xs) (¬Px ∷ All¬) (there AnyP) = from xs All¬ AnyP
  
  from∘to : {A : Set} {P : A → Set} (xs : List A) → ∀ (¬Any) →
    from {A} {P} xs (to xs ¬Any) ≡ ¬Any
  from∘to xs ¬Any = extensionality λ AnyP → ⊥-elim (¬Any AnyP)

  to∘from : {A : Set} {P : A → Set} (xs : List A) → ∀ (All¬) →
    to {A} {P} xs (from xs All¬) ≡ All¬
  to∘from [] [] = refl
  to∘from (x ∷ xs) (¬Px ∷ ¬Pxs) = cong (¬Px ∷_) (to∘from xs ¬Pxs)

-- ¬All≃Any¬ : ∀ {A : Set} (P : A → Set) (xs : List A)
--  → (¬_ ∘′ All P) xs ≃ Any (¬_ ∘′ P) xs
-- doesn't hold, because we couldn't use
-- ((¬_ ∘′ All P) xs) to construct a (Any (¬_ ∘′ P) xs)

------------------------------

all : ∀ {A : Set} → (A → Bool) → List A → Bool
all p  =  foldr _∧_ true ∘ map p

Decidable : ∀ {A : Set} → (A → Set) → Set
Decidable {A} P  =  ∀ (x : A) → Dec (P x)

All? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (All P)
All? P? []                                 = yes []
All? P? (x ∷ xs) with P? x   | All? P? xs
...                 | yes Px | yes p₁      = yes (Px ∷ p₁)
...                 | no ¬Px | _           = no λ{ (Px ∷ Pxs) → ¬Px Px}
...                 | _      | no ¬Pxs     = no λ{ (Px ∷ Pxs) → ¬Pxs Pxs}

---------- practice ----------
any : ∀ {A : Set} → (A → Bool) → List A → Bool
any p  =  foldr _∨_ false ∘ map p

Any? : ∀ {A : Set} {P : A → Set} → Decidable P → Decidable (Any P)
Any? P? [] = no (λ ())
Any? P? (x ∷ xs) with P? x   | Any? P? xs
Any? P? (x ∷ xs)    | yes Px | _        = yes (here Px)
Any? P? (x ∷ xs)    | _      | yes ∃Pxs = yes (there ∃Pxs)
Any? P? (x ∷ xs)    | no ¬Px | no ¬∃Pxs = no λ{ (here Px) → ¬Px Px
                                              ; (there ∃Px) → ¬∃Pxs ∃Px
                                              }

open import plfa-code.Quantifiers using (∀-extensionality)

-- the implicit argument x is too difficult to deal with ..
-- so I replace it with explicit

All-∀ : ∀ {A : Set} {P : A → Set} (xs : List A) →
  All P xs ≃ (∀ (x) → x ∈ xs → P x)
All-∀ {A} {P} xs =
  record
  { to      = to xs
  ; from    = from xs
  ; from∘to = from∘to xs
  ; to∘from = to∘from xs
  }
  where
  to : ∀ {A : Set} {P : A → Set} (xs : List A) →
    All P xs → (∀ (x) → x ∈ xs → P x)
  to (x₁ ∷ xs) (Px₁ ∷  _ ) .x₁ (here refl)  = Px₁
  to (x₁ ∷ xs) ( _  ∷ Pxs) x   (there x∈xs) = to xs Pxs x x∈xs

  from : ∀ {A : Set} {P : A → Set} (xs : List A) →
    (∀ (x) → x ∈ xs → P x) → All P xs
  from [] f = []
  from (x ∷ xs) f = f x (here refl) ∷ from xs (λ x₁ → (f x₁) ∘ there)

  from∘to : ∀ {A : Set} {P : A → Set} (xs : List A) →
    (Pxs : All P xs) → from xs (to xs Pxs) ≡ Pxs
  from∘to [] [] = refl
  from∘to (x ∷ xs) (Px ∷ Pxs) = cong (Px ∷_) (from∘to xs Pxs)

  to∘from : {A : Set} {P : A → Set} (xs : List A) →
    (f : (∀ (x) → x ∈ xs → P x)) → to xs (from xs f) ≡ f
  to∘from [] f = ∀-extensionality (to [] []) f
    (λ x → ∀-extensionality (to [] [] x) (f x) λ ())
  to∘from (x ∷ xs) f = ∀-extensionality (to (x ∷ xs) (from (x ∷ xs) f)) f
    (λ x₁ → ∀-extensionality (to (x ∷ xs) (from (x ∷ xs) f) x₁) (f x₁)
      λ{ (here refl) → refl
       ; (there x₁∈xs) → cong (λ g → g x₁ x₁∈xs)
                (to∘from xs ((λ x₂ x₃ → f x₂ (there x₃))))
       }
    )

-- Emmmm..., "∃[ x ∈ xs ] P x" is not a valid type, I guess its real
-- meaning is like below

Any-∃ : {A : Set} {P : A → Set} (xs : List A) →
  Any P xs ≃ ∃[ x ] (x ∈ xs × P x)
Any-∃ xs =
  record
  { to      = to xs
  ; from    = from xs
  ; from∘to = from∘to xs
  ; to∘from = to∘from xs
  }
  where
  to : {A : Set} {P : A → Set} (xs : List A) →
    Any P xs → ∃[ x ] (x ∈ xs × P x)
  to (x ∷ xs) (here Px) = ⟨ x , ⟨ here refl , Px ⟩ ⟩
  to (x ∷ xs) (there AnyP) with to xs AnyP
  ... | ⟨ x₁ , ⟨ x₁∈xs , Px ⟩ ⟩ = ⟨ x₁ , ⟨ there x₁∈xs , Px ⟩ ⟩

  from : {A : Set} {P : A → Set} (xs : List A) →
    ∃[ x ] (x ∈ xs × P x) → Any P xs
  from (x ∷ xs) ⟨ .x , ⟨ here refl   , Px  ⟩ ⟩ = here Px
  from (x ∷ xs) ⟨ x₁ , ⟨ there x₁∈xs , Px₁ ⟩ ⟩ =
    there (from xs ⟨ x₁ , ⟨ x₁∈xs , Px₁ ⟩ ⟩)

  from∘to : {A : Set} {P : A → Set} (xs : List A) →
    (AnyP : Any P xs) → from xs (to xs AnyP) ≡ AnyP
  from∘to (x ∷ xs) (here x₁) = refl
  from∘to (x ∷ xs) (there AnyP) = cong there (from∘to xs AnyP)

  to∘from : {A : Set} {P : A → Set} (xs : List A) →
    (∃Pxs : ∃[ x ] (x ∈ xs × P x)) → to xs (from xs ∃Pxs) ≡ ∃Pxs
  to∘from (x ∷ xs) ⟨ .x , ⟨ here refl   , Px  ⟩ ⟩ = refl
  to∘from {A} {P} (x ∷ xs) ⟨ x₁ , ⟨ there x₁∈xs , Px₁ ⟩ ⟩
    = cong (λ a → ⟨ proj₁ a , ⟨ there (proj₁ (proj₂ a)) , proj₂ (proj₂ a) ⟩ ⟩)
           (to∘from {A} {P} xs ⟨ x₁ , ⟨ x₁∈xs , Px₁ ⟩ ⟩)

filter? : ∀ {A : Set} {P : A → Set}
  → (P? : Decidable P) → List A → ∃[ ys ]( All P ys )
filter? P? [] = ⟨ [] , [] ⟩
filter? P? (x ∷ xs) with P? x | filter? P? xs
...                  | yes Px | ⟨ ys , Pys ⟩  = ⟨ (x ∷ ys) , (Px ∷ Pys) ⟩
...                  | no ¬Px | ∃ys∀Pys       = ∃ys∀Pys
