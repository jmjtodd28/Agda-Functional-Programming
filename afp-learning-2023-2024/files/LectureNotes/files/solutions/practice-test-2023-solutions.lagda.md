# Class Test 1 Solutions

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module solutions.practice-test-2023-solutions where

open import prelude
open import natural-numbers-functions
open import List-functions
open import isomorphisms
```
## Question 1

```agda
ite-fact₁ : (b : Bool) → if b then true else false ≡ b
ite-fact₁ true  = refl true
ite-fact₁ false = refl false

ite-fact₂ : {X : Type} {x : X} (b : Bool) → if b then x else x ≡ x
ite-fact₂ true  = refl _
ite-fact₂ false = refl _

ite-fact₃ : {X : Type} {x y : X} (b : Bool)
          → if b then x else y ≡ if not b then y else x
ite-fact₃ true  = refl _
ite-fact₃ false = refl _

ite-fact₄ : {X : Type} {x y u v : X} (a b : Bool)
          → if a then (if b then x else y) else (if b then u else v)
          ≡ if b then (if a then x else u) else (if a then y else v)
ite-fact₄ true  b = refl _
ite-fact₄ false b = refl _
```

## Question 2

```agda
data _is-bounded-by_ : List ℕ → ℕ → Type where
  zero-bounds-[] : [] is-bounded-by 0
  stays-bounded : {b : ℕ} → (n : ℕ) (ns : List ℕ)
    → ns is-bounded-by b
    → n ≤₁ b
    → (n :: ns) is-bounded-by b
  bound-increases : {b : ℕ} → (n : ℕ) (ns : List ℕ)
    → ns is-bounded-by b
    → ¬ (n ≤₁ b)
    → (n :: ns) is-bounded-by n
```

**Prove** the following examples involving `is-bounded-by`:

```agda
bounded-inductive-example₀ : [] is-bounded-by 0
bounded-inductive-example₀ = zero-bounds-[]

bounded-inductive-example₁ : (2 :: 1 :: [ 3 ]) is-bounded-by 3
bounded-inductive-example₁ =
  stays-bounded 2 (1 :: [ 3 ])
                (stays-bounded 1 [ 3 ]
                               (bound-increases 3 [] zero-bounds-[]
                                                𝟘-is-empty)
                               ⋆)
                ⋆

bounded-inductive-example₂ : ¬ ((3 :: 2 :: [ 1 ]) is-bounded-by 2)
bounded-inductive-example₂ (stays-bounded .3 .(2 :: [ 1 ]) h p) = p
```

## Question 3

```agda
×-second-equation : (X Y : Type) → (X ∔ 𝟙) × Y ≅ (X × Y) ∔ Y
×-second-equation X Y =
 record { bijection  = f
        ; bijectivity = record { inverse = g ; η = section ; ε = retraction } }
  where
   f : (X ∔ 𝟙) × Y → (X × Y) ∔ Y
   f (inl x , y) = inl (x , y)
   f (inr ⋆ , y) = inr y

   g : (X × Y) ∔ Y → (X ∔ 𝟙) × Y
   g (inl (x , y)) = (inl x , y)
   g (inr       y) = (inr ⋆ , y)

   section : g ∘ f ∼ id
   section (inl x , y) = refl _
   section (inr ⋆ , y) = refl _

   retraction : f ∘ g ∼ id
   retraction (inl (x , y)) = refl _
   retraction (inr       y) = refl _
```

## Question 4

```agda
data _∈_ {X : Type} : X → List X → Type where
  head-case : (x : X) (xs : List X) → x ∈ (x :: xs)
  tail-case : (x : X) (xs : List X) → x ∈ xs → (y : X) → x ∈ (y :: xs)

mapped-membership : Type → Type → Type
mapped-membership X Y
 = (x : X) (xs : List X) (f : X → Y) → x ∈ xs → f x ∈ map f xs
```

## Question 5

```agda
is-idempotent : {X : Type} (f : X → X) → Type
is-idempotent {X} f = (x : X) → f (f x) ≡ f x

map-of-idempotent-function-is-idempotent : {X : Type} (f : X → X)
                                         → is-idempotent f
                                         → is-idempotent (map f)
map-of-idempotent-function-is-idempotent {X} f f-ip []        = refl []
map-of-idempotent-function-is-idempotent {X} f f-ip (x :: xs) =
 f (f x) :: map f (map f xs) ≡⟨ ap (_:: map f (map f xs)) (f-ip x) ⟩
 f x     :: map f (map f xs) ≡⟨ ap (f x ::_) IH ⟩
 f x     :: map f xs         ∎
  where
   IH : map f (map f xs) ≡ map f xs
   IH = map-of-idempotent-function-is-idempotent f f-ip xs
```
