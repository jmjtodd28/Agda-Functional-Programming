<!--
```agda
{-# OPTIONS --without-K --safe #-}

module strict-total-order-rewrite where

open import prelude
open import decidability
open import natural-numbers-functions
             renaming (_≤_ to _≤ₙ_;
                       _≥_ to _≥ₙ ;
                       max to maxₙ ;
                       min to minₙ)
open import List-functions

record StrictTotalOrder (X : Type) : Type₁ where
  field
    _<_ : X → X → Type

    irreflexive : (x : X) → ¬ (x < x)
    transitive : {x y z : X} → x < y → y < z → x < z
    connected : {x y : X} → ¬ (x ≡ y) → (x < y) ∔ (y < x)

    ≡-is-decidable : has-decidable-equality X

  _>_ : X → X → Type
  x > y = y < x

  _≤_ : X → X → Type
  x ≤ y = (y ≡ x) ∔ (x < y)

  _≥_ : X → X → Type
  x ≥ y = y ≤ x

  irreflexive' : (x y : X) → x ≡ y → ¬ (x < y)
  irreflexive' x .x (refl .x) q = (irreflexive x) q 

  antisymmetric : (x y : X) → x < y → ¬ (y < x)
  antisymmetric x y p q = irreflexive y (transitive q p)

  trichotomy : (x y : X) → (x < y) ∔ ((x ≡ y) ∔ (y < x))
  trichotomy x y with ≡-is-decidable x y
  ... | inl x≡y = inr (inl x≡y)
  ... | inr b with connected b
  ... | inl x<y = inl x<y
  ... | inr x>y = inr (inr x>y)

  not-<-and-not-≡-give-> : (x y : X) → ¬ (x < y) → ¬ (x ≡ y) → y < x
  not-<-and-not-≡-give-> x y p q with connected q
  ... | inl x<y = 𝟘-elim (p x<y)
  ... | inr y<x = y<x

  not-<-gives-≥ : (x y : X) → ¬ (x < y) → x ≥ y
  not-<-gives-≥ x y p with trichotomy x y
  ... | inl x<y = 𝟘-elim (p x<y)
  ... | inr (inl x≡y) = inl x≡y
  ... | inr (inr x>y) = inr x>y

  <-is-decidable : (x y : X) → is-decidable (x < y)
  <-is-decidable x y with ≡-is-decidable x y
  ... | inl x≡y = inr (irreflexive' x y x≡y)
  ... | inr ¬x≡y with trichotomy x y
  ... | inl x<y = inl x<y
  ... | inr (inl x≡y) = 𝟘-elim (¬x≡y x≡y)
  ... | inr (inr x>y) = inr ((antisymmetric y x) x>y) 

  ≤-is-decidable : (x y : X) → is-decidable (x ≤ y)
  ≤-is-decidable x y = ∔-preserves-decidability (≡-is-decidable y x) (<-is-decidable x y)

  max : X → X → X
  max x y with <-is-decidable x y
  max x y | inl x<y  = y
  max x y | inr ¬x<y = x

  max-upper-boundₗ : (x y : X) → x ≤ max x y
  max-upper-boundₗ x y with <-is-decidable x y
  ... | inl x<y = inr x<y
  ... | inr ¬x<y = inl (refl x)

  max-upper-boundᵣ : (x y : X) → y ≤ max x y
  max-upper-boundᵣ x y with <-is-decidable x y
  ... | inl x<y = inl (refl y)
  ... | inr ¬x<y with trichotomy x y
  ... | inl x<y = 𝟘-elim (¬x<y x<y)
  ... | inr (inl x≡y) = inl x≡y
  ... | inr (inr x>y) = inr x>y

  max-least-upper-bound : (x y u : X) → y ≤ u → x ≤ u → max x y ≤ u
  max-least-upper-bound x y u p q with <-is-decidable x y
  ... | inl x<y = p
  ... | inr ¬x<y = q

  min : X → X → X
  min x y with <-is-decidable x y
  min x y | inl x<y  = x
  min x y | inr ¬x<y = y


  data _<ₙ_ : ℕ → ℕ → Type where
    <-zero : {n : ℕ} → zero <ₙ suc n
    <-suc  : {n m : ℕ} → n <ₙ m → suc n <ₙ suc m

  <ₙ-trans : {x y z : ℕ} → x <ₙ y → y <ₙ z → x <ₙ z
  <ₙ-trans <-zero (<-suc y<z) = <-zero
  <ₙ-trans (<-suc x<y) (<-suc y<z) = <-suc (<ₙ-trans x<y y<z)


  <ₙ-irreflexive : (x : ℕ) → ¬ (x <ₙ x)
  <ₙ-irreflexive .(suc _) (<-suc p) = <ₙ-irreflexive _ p

  <ₙ-connected : {x y : ℕ} → ¬ (x ≡ y) → (x <ₙ y) ∔ (y <ₙ x)
  <ₙ-connected {zero} {zero} p = 𝟘-elim (p (refl zero))
  <ₙ-connected {zero} {suc y} p = inl <-zero
  <ₙ-connected {suc x} {zero} p = inr <-zero
  <ₙ-connected {suc x} {suc y} p = {!!}
```
