<!--
```agda
{-# OPTIONS --without-K --safe #-}

open import prelude

module insertion-sort-lecture (X : Type) where

open import isomorphisms
open import decidability
open import List-functions
open import iso-utils
```
-->

## Strict total order

```agda
record StrictTotalOrder (X : Type) : Type₁ where
  field
    _<_ : X → X → Type

    irreflexive : (x : X) → ¬ (x < x)
    transitive : {x y z : X} → x < y → y < z → x < z
    connected : {x y : X} → ¬ (x ≡ y) → (x < y) ∔ (y < x)

    decidable : has-decidable-equality X

  antisymmetric : (x y : X) → x < y → ¬ (y < x)
  antisymmetric x y x<y y<x = {!!}

  trichotomy : (x y : X) → (x < y) ∔ ((x ≡ y) ∔ (y < x))
  trichotomy x y = {!!}

data _<ₙ_ : ℕ → ℕ → Type where
  <-zero : {n : ℕ} → zero <ₙ suc n
  <-suc : {n m : ℕ} → n <ₙ m → suc n <ₙ suc m

<ₙ-trans : {x y z : ℕ} → x <ₙ y → y <ₙ z → x <ₙ z
<ₙ-trans = {!!}

<ₙ-irreflexive : (x : ℕ) → ¬ (x <ₙ x)
<ₙ-irreflexive = {!!}

<ₙ-connected : {x y : ℕ} → ¬ (x ≡ y) → (x <ₙ y) ∔ (y <ₙ x)
<ₙ-connected = {!!}

ℕ-StrictTotalOrder : StrictTotalOrder ℕ
ℕ-StrictTotalOrder =
  record
    { _<_ = _<ₙ_
    ; decidable = ℕ-has-decidable-equality
    ; irreflexive = <ₙ-irreflexive
    ; transitive = <ₙ-trans
    ; connected = <ₙ-connected
    }
```

## Sorted lists

```agda
module _ {X : Type} (τ : StrictTotalOrder X) where

  open StrictTotalOrder τ

  data Sorted : List X → Set where
    nil-sorted : Sorted []
    sing-sorted : {x : X} → Sorted (x :: [])
    adj-sorted : {y x : X} {xs : List X}
      → Sorted (x :: xs)
      → (x ≡ y) ∔ (y < x)
      → Sorted (y :: x :: xs)
```

## A specification of sorting algorithms

<!--
```agda
module _ where
  private
```
-->
```agda
    SortingAlgorithm : (X : Type) (τ : StrictTotalOrder X) → Type
    SortingAlgorithm X τ = Σ sort ꞉ (List X → List X) ,
                             ((xs : List X) → Sorted τ (sort xs))
```

Serious problem:

```agda
    TrivialSorting : (X : Type) (τ : StrictTotalOrder X) → SortingAlgorithm X τ
    TrivialSorting X τ = (λ _ → []) , λ _ → nil-sorted
```

We clearly need some way to exclude this kind of trivial example.

## Permutations

```agda
Pos : {X : Type} → List X → Type
Pos [] = 𝟘
Pos (_ :: xs) = 𝟙 ∔ Pos xs

Inhab : {X : Type} (l : List X) → Pos l → X
Inhab (x :: _) (inl ⋆) = x
Inhab (_ :: l) (inr p) = Inhab l p

open _≅_

record _IsPermutationOf_ {X : Type} (xs ys : List X) : Type where
  field
    pos-iso : Pos xs ≅ Pos ys
    inhab-eq : (p : Pos xs) → Inhab xs p ≡ Inhab ys (bijection pos-iso p)
```

##  Sorting Algorithms

```agda
record SortingAlgorithm {X : Type} (τ : StrictTotalOrder X) : Type where
  field
    sort : List X → List X
    sort-is-sorted : (xs : List X) → Sorted τ (sort xs)
    sort-is-permutation : (xs : List X) → (sort xs) IsPermutationOf xs
```

## Example: Insertion Sort

```agda
module _ (τ : StrictTotalOrder X) where

 open _IsPermutationOf_
 open StrictTotalOrder τ
 open _≅_

 insert : X → List X → List X
 insert y xs = {!!}

 insert-all : List X → List X → List X
 insert-all xs ys = {!!}

 insertion-sort : List X → List X
 insertion-sort xs = {!!}
```

## Proving the insertion produces a sorted list

The goal here is to prove `insertion-sort-is-sorted`, but we first
need to prove a few intuitive facts about the helpers functions used
for that purpose:


```agda
 insert-is-sorted : (y : X) (xs : List X)
                  → Sorted τ xs
                  → Sorted τ (insert y xs)
 insert-is-sorted y xs srtd = {!!}

 insert-all-is-sorted : (xs ys : List X) (ys-srtd : Sorted τ ys)
                      → Sorted τ (insert-all xs ys)
 insert-all-is-sorted xs ys ys-srtd = {!!}

 insertion-sort-is-sorted : (xs : List X)
                          → Sorted τ (insertion-sort xs)
 insertion-sort-is-sorted xs = {!!}
```

## Constructing the Permutation: technical lemmas

Important: we need to construct the right permutation, not just any
permutation.

The goal here is to prove `insertion-sort-is-perm`. Again we need to prove some lemmas for that purpose, but they a somewhat technical, and less intuitive at first sight:

```agda
 insert-pos-iso : (x : X) (xs : List X)
                → Pos (insert x xs) ≅ 𝟙 ∔ Pos xs
 insert-pos-iso y xs = {!!}

 insert-all-pos-iso : (xs ys : List X)
                    → Pos (insert-all xs ys) ≅ Pos (xs ++ ys)
 insert-all-pos-iso xs ys = {!!}

 pos-swap-lemma : (x y : X) (xs : List X)
  → (p : Pos (y :: xs))
  → Inhab (x :: y :: xs) (inr p)
  ≡ Inhab (y :: x :: xs) (bijection (∔-left-swap-iso 𝟙 𝟙 (Pos xs)) (inr p))
 pos-swap-lemma x y xs p = {!!}

 insert-inhab-eq : (y : X) (xs : List X)
                 → (p : Pos (insert y xs))
                 → Inhab (insert y xs) p
                 ≡ Inhab (y :: xs) (bijection (insert-pos-iso y xs) p)
 insert-inhab-eq y xs p = {!!}

 inhab-ext-lemma : (x : X) (xs ys : List X)
  → (α : Pos xs ≅ Pos ys)
  → (e : (p : Pos xs) → Inhab xs p
                      ≡ Inhab ys (bijection α p))
  → (p : Pos (x :: xs)) → Inhab (x :: xs) p
                        ≡ Inhab (x :: ys) (bijection (∔-pair-iso (id-iso 𝟙) α) p)
 inhab-ext-lemma x xs ys α e p = {!!}

 insert-all-inhab-eq : (xs ys : List X) (p : Pos (insert-all xs ys))
  → Inhab (insert-all xs ys) p
  ≡ Inhab (xs ++ ys) (bijection (insert-all-pos-iso xs ys) p)
 insert-all-inhab-eq xs ys p = {!!}

 insert-is-perm : (x : X) (xs : List X)
                → (insert x xs) IsPermutationOf (x :: xs)
 insert-is-perm x xs = {!!}
```

## Constructing the Permutation

```agda
 insertion-sort-is-perm : (xs : List X)
                        → (insertion-sort xs) IsPermutationOf xs
 insertion-sort-is-perm xs = {!!}
```

## The correctness of insertion sort

```agda
 insertion-sort-algorithm : SortingAlgorithm τ
 insertion-sort-algorithm =
   record { sort = insertion-sort
          ; sort-is-sorted = insertion-sort-is-sorted
          ; sort-is-permutation = insertion-sort-is-perm
          }
```
