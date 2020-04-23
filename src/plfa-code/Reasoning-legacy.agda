module plfa-code.Reasoning-legacy where

import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl; trans)

infixr 2 _≡⟨_⟩_
infix  3 _∎

_≡⟨_⟩_ : ∀ {A : Set} (x : A) {y z : A}
  → x ≡ y
  → y ≡ z
    -------
  → x ≡ z
x ≡⟨ x≡y ⟩ y≡z  =  trans x≡y y≡z

_∎ : ∀ {A : Set} (x : A)
    ------
  → x ≡ x
x ∎  = refl
