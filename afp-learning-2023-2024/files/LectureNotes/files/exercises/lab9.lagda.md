# Week 9 - Lab Sheet

```agda
{-# OPTIONS --safe --without-K --auto-inline #-}

module exercises.lab9 where

open import prelude
open import decidability
open import Fin
open import List-functions
open import isomorphisms
open import sorting
open import strict-total-order

open import solutions.lab8
```

For all of the following questions we will work with a type `X` that
has decidable equality and a strict total order `_<_`.

```agda
module _
        {X : Type}
        (sto : StrictTotalOrder X)
       where

 open StrictTotalOrder sto
```

## Exercise 1

In the [lecture notes](../sorting.lagda.md) the type `Pos xs` was
introduced for every list `xs : List X`.

This is the type of positions in the list; for example, the type
`Pos (1 :: 2 :: [ 3 ])` has elements `inl ⋆`, `inr (inl ⋆)` and
`inr (inr (inl ⋆))`, representing the first, second and third elements
of the list, respectively.

Given any list `xs : List X`, there is a natural ordering of its
positions.

**Define** this strict total order.

```agda
 _<[Pos]_ : {X : Type} {xs : List X} → Pos xs → Pos xs → Type
 _<[Pos]_ = {!!}
```

## Exercise 2

We give some facts about the type `Y ∔ Z` for any types `Y` and `Z`:

 1. `inl y` does not equal `inr z` (for all `y : Y` and `z : Z`),
 1. `inr z` does not equal `inl y` (for all `y : Y` and `z : Z`),
 1. If `inl y₁ ≡ inl y₂` then `y₁ ≡ y₂` (for all `y₁,y₂ : Y`),
 1. If `inr z₁ ≡ inr z₂` then `z₁ ≡ z₂` (for all `z₁,z₂ : Z`).

```agda
 inl-is-not-inr : {Y Z : Type} {y : Y} {z : Z}
                → ¬ (inl {Y} {Z} y ≡ inr {Y} {Z} z)
 inl-is-not-inr ()

 inr-is-not-inl : {Y Z : Type} {y : Y} {z : Z}
                → ¬ (inr {Y} {Z} z ≡ inl {Y} {Z} y)
 inr-is-not-inl ()

 inl-lc : {Y Z : Type} {y₁ y₂ : Y}
        → inl {Y} {Z} y₁ ≡ inl {Y} {Z} y₂ → y₁ ≡ y₂
 inl-lc (refl _) = refl _

 inr-lc : {Y Z : Type} {z₁ z₂ : Z}
        → inr {Y} {Z} z₁ ≡ inr {Y} {Z} z₂ → z₁ ≡ z₂
 inr-lc (refl _) = refl _
```

Using the facts above, **prove** that if both `Y` and `Z` have
[decidable equality](../decidability.lagda.md), then so does `Y ∔ Z`.

```agda
 +-has-decidable-equality : {Y Z : Type}
                          → has-decidable-equality Y
                          → has-decidable-equality Z
                          → has-decidable-equality (Y ∔ Z)
 +-has-decidable-equality = {!!}
```

## Exercise 3

`_<[Pos]_` defined in Exercise 1 must satisfy all the necessary
properties of a strict total order:
  * `Pos xs` has decidable equality,
  * `_<[Pos]_` is irreflexive,
  * `_<[Pos]_` is transitive,
  * `_<[Pos]_` is connected.

**Prove** that it does.

```agda
 𝟙-has-decidable-equality : has-decidable-equality 𝟙
 𝟙-has-decidable-equality = {!!}
 
 <[Pos]-decidable : {xs : List X} → has-decidable-equality (Pos xs)
 <[Pos]-decidable = {!!}

 <[Pos]-irreflexive : {xs : List X} → (x : Pos xs) → ¬ (x <[Pos] x)
 <[Pos]-irreflexive = {!!}

 <[Pos]-transitive : {xs : List X} → {n m o : Pos xs}
                   → n <[Pos] m → m <[Pos] o → n <[Pos] o
 <[Pos]-transitive = {!!}
 
 <[Pos]-connected : {xs : List X} → {n m : Pos xs}
                  → ¬ (n ≡ m) → (n <[Pos] m) ∔ (m <[Pos] n)
 <[Pos]-connected = {!!}

 STO : (xs : List X) → StrictTotalOrder (Pos xs)
 STO xs = record
           { _<_ = _<[Pos]_
           ; irreflexive = <[Pos]-irreflexive
           ; transitive = λ {n} {m} {o} → <[Pos]-transitive {xs} {n} {m} {o}
           ; connected = <[Pos]-connected
           ; ≡-is-decidable = <[Pos]-decidable {xs}
           } 
```

## Exercise 4

As you saw in [last week's lab sheet](../solutions/lab8.lagda.md),
every strict total order `_<_` has an associated non-strict total
order `_≤_`, defined `x ≤ y = (y ≡ x) ∔ (x < y)`.

We use this fact to extract `_≤_` on `X` and `_≤[Pos}_` on `Pos xs`
given any list `xs : List X`.

```agda 
 nsto : NonStrictTotalOrder X
 nsto = non-strict-total-order-from-strict-total-order sto

 NSTO : (xs : List X) → NonStrictTotalOrder (Pos xs)
 NSTO xs = non-strict-total-order-from-strict-total-order (STO xs)

 -- _≤_ : X → X → Type
 -- _≤_ = NonStrictTotalOrder._≤_ nsto

 _≤[Pos]_ : {xs : List X} → Pos xs → Pos xs → Type
 _≤[Pos]_ {xs} = NonStrictTotalOrder._≤_ (NSTO xs)

 ≤-reflexive : (x : X) → x ≤ x
 ≤-reflexive = NonStrictTotalOrder.reflexive nsto

 ≤-transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
 ≤-transitive = NonStrictTotalOrder.transitive nsto
```

Given any types `X` and `Y` equipped with non-strict total orders
`_≤X_` and `_≤Y_` respectively, we define the notion of a *monotonic
function*.

A function `f : X → Y` is monotonic if as the arguments increase (or
stay the same), the value of the function at the argument also
increases (or stays the same).

```agda
 monotonic : {X Y : Type}
           → NonStrictTotalOrder X → NonStrictTotalOrder Y
           → (f : X → Y) → Type
 monotonic {X} {Y} nstox nstoy f = (x y : X) → x ≤X y → f x ≤Y f y
   where
     _≤X_ = NonStrictTotalOrder._≤_ nstox
     _≤Y_ = NonStrictTotalOrder._≤_ nstoy
```

The `Inhab : Pos xs → X` function
[from the lecture notes](../sorting.lagda.md) is a monotonic function
when `xs` is a Sorted list: i.e., as the position argument increases
(or stays the same), the inhabitant obtained from the list also
increases (or stays the same).

To state this mathematically, we want to prove that if `n ≤[Pos] m`
then `Inhab xs n ≤ Inhab xs m`.

First we will prove two small lemmas.

### Exercise 4.1

**Prove** that if a list `(x :: xs)` is sorted, then the list `xs` is
also sorted.

```agda
 tail-sorted : (x : X) (xs : List X)
             → Sorted sto (x :: xs)
             → Sorted sto       xs            
 tail-sorted = {!!}
```

### Exercise 4.2

**Prove** that if a list `(x :: y :: xs)` is sorted, then the list
`(x :: xs)` is also sorted.

```agda
 drop-one-sorted : (x y : X) (xs : List X)
                 → Sorted sto (x :: y :: xs)
                 → Sorted sto (x      :: xs)
 drop-one-sorted = {!!}
```

### Exercise 4.3

**Prove** that, given a sorted list `xs`, `Inhab xs` is monotonic.

```agda
 Inhab-monotonic : (xs : List X) → Sorted sto xs
                   → monotonic (NSTO xs) nsto (Inhab xs)                   
 Inhab-monotonic = {!!}
```

## Exercise 5

Recall the alternate definition of sorted list given in the lecture:

```agda

 open _≅_

 data SortedList : Type
 prependable : X → SortedList → Type

 data SortedList where
   nil : SortedList
   cons : (x : X) (xs : SortedList)
     → prependable x xs → SortedList

 prependable x₀ nil = 𝟙
 prependable x₀ (cons x xs _) = x₀ ≤ x

 Posₛ : SortedList → Type
 Posₛ nil = 𝟘
 Posₛ (cons _ xs _) = 𝟙 ∔ Posₛ xs

 _!!ₛ_ : (xs : SortedList) → Posₛ xs → X
 cons x xs ρ !!ₛ inl ⋆ = x
 cons x xs ρ !!ₛ inr p = xs !!ₛ p

``` 

### Exercise 5.1

In order to better understand the presentation of insertion sort using
this definition, **redo** the definitions from the lecture:

```agda

 insert : X → SortedList → SortedList
 insert-lem : (x₀ x : X) (xs : SortedList)
   → (ρ : prependable x xs)
   → x < x₀
   → prependable x (insert x₀ xs)

 insert = {!!}
 insert-lem = {!!}
 
 insert-all : List X → SortedList → SortedList
 insert-all = {!!} 

 insertion-sort : List X → SortedList
 insertion-sort xs = insert-all xs nil 

```

### Exercise 5.2

Now prove the compatibilites between insertion and positions:

```agda
 insert-pos-lem : (x : X) (xs : SortedList)
   → 𝟙 ∔ Posₛ xs ≅ Posₛ (insert x xs) 
 insert-pos-lem = {!!} 

 insert-pos-lem-left : (x : X) (xs : SortedList)
   → x ≡ insert x xs !!ₛ bijection (insert-pos-lem x xs) (inl ⋆) 
 insert-pos-lem-left = {!!} 

 insert-pos-lem-right : (x : X) (xs : SortedList) (p : Posₛ xs)
   → xs !!ₛ p ≡ (insert x xs !!ₛ bijection (insert-pos-lem x xs) (inr p) )
 insert-pos-lem-right  = {!!}

 insertion-pos-iso : (xs : List X) → Pos xs ≅ Posₛ (insertion-sort xs)
 insertion-pos-iso = {!!} 
```

### Exercise 5.3

Finally, prove that the isomorphism constructred above respects inhabitants:

```agda
 _!!_ : (xs : List X) → Pos xs → X
 xs !! p = Inhab xs p

 insertion-inhab : (xs : List X) (p : Pos xs)
   → xs !! p ≡ (insertion-sort xs !!ₛ bijection (insertion-pos-iso xs) p)
 insertion-inhab = {!!} 
```
