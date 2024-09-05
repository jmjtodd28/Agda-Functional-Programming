# Practice Test

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.practice-test-2023 where

open import prelude
open import natural-numbers-functions
open import List-functions
open import isomorphisms
```

## Important remarks
1. Put your student ID card on your desk.
1. You are not allowed to talk or use your phone during the test. If you do,
this will be considered an instance of plagiarism.
1. You can use a web-browser only for reading the lecture notes and the Agda
manual. If you use it for anything else, this will be considered an instance
of plagiarism.
1. Please do not ask questions to the invigilators unless you think there is a
mistake in the test.
1. You can do these questions in any order. In particular, if you cannot work
out the proof of something, you can leave the hole empty and still use it in
other questions and get full marks for those other questions.
1. Each of the five sections has equal weight (20% each).
1. Your answers will be marked on correctness *and* quality.
1. The test starts at 16:00. For students with extra time, your test starts at 15:30.
All students finish at 17:50, with 5% penalty for submissions at 18:00. No submissions are possible after 18:00, to make sure you submit before 18:00.
1. You must not leave the room between 17:40 and 17:50 to avoid disruption.

## Please check your Canvas submission after you have submitted

This is necessary to make sure you submitted the file you intended to submit. Often students accidentally submit the wrong file.

It is also a good idea to submit to Canvas well before the deadline when you have completed enough questions. We will mark the latest submission.

## Question 1

**Prove** the following facts about `if_then_else_`:

```agda
ite-fact₁ : (b : Bool) → if b then true else false ≡ b
ite-fact₁ = {!!}

ite-fact₂ : {X : Type} {x : X} (b : Bool) → if b then x else x ≡ x
ite-fact₂ = {!!}

ite-fact₃ : {X : Type} {x y : X} (b : Bool)
          → if b then x else y ≡ if not b then y else x
ite-fact₃ = {!!}

ite-fact₄ : {X : Type} {x y u v : X} (a b : Bool)
          → if a then (if b then x else y) else (if b then u else v)
          ≡ if b then (if a then x else u) else (if a then y else v)
ite-fact₄ = {!!}
```

## Question 2

In this exercise, we will define an inductive type expressing what the least
upperbound of a list is.

More precisely, `xs is-bounded-by b` should satisfy:
- every element of `xs` is less than or equal to `b`;
- if `b'` is another element with the above property, then `b` is less than
or equal to `b'`.

So, for example, `[5 , 8 , 2]` is bounded by 8, but not by 9, 10, 11, ...
because these numbers are strictly bigger than necessary.

By definition, the empty list is bounded by 0.

**Complete** the definition of the inductively defined type.

```agda
data _is-bounded-by_ : List ℕ → ℕ → Type where
  zero-bounds-[] : {!!}
  stays-bounded : {b : ℕ} → (n : ℕ) (ns : List ℕ)
    → {!!}
    → n ≤₁ b
    → {!!} is-bounded-by {!!}
  bound-increases : {b : ℕ} → (n : ℕ) (ns : List ℕ)
    → {!!}
    → ¬ (n ≤₁ b)
    → {!!} is-bounded-by {!!}
```

**Prove** the following examples involving `is-bounded-by`:

```agda
bounded-inductive-example₀ : [] is-bounded-by 0
bounded-inductive-example₀ = {!!}

bounded-inductive-example₁ : (2 :: 1 :: [ 3 ]) is-bounded-by 3
bounded-inductive-example₁ = {!!}

bounded-inductive-example₂ : ¬ ((3 :: 2 :: [ 1 ]) is-bounded-by 2)
bounded-inductive-example₂ = {!!}
```

## Question 3

The cartesian product `×` satisfies the same equations as multiplication of
natural numbers:
1. `𝟘 × X ≅ X` for every type `X`;
1. `(X ∔ 𝟙) × Y ≅ (X × Y) ∔ Y` for every two types `X` and `Y`.

**Prove** the second isomorphism.

```agda
×-second-equation : (X Y : Type) → (X ∔ 𝟙) × Y ≅ (X × Y) ∔ Y
×-second-equation X Y =
 record { bijection  = f
        ; bijectivity = record { inverse = g ; η = section ; ε = retraction } }
  where
   f : (X ∔ 𝟙) × Y → (X × Y) ∔ Y
   f = {!!}

   g : (X × Y) ∔ Y → (X ∔ 𝟙) × Y
   g = {!!}

   section : g ∘ f ∼ id
   section = {!!}

   retraction : f ∘ g ∼ id
   retraction = {!!}
```

## Question 4

We can define the list membership relation `∈` as follows:

```agda
data _∈_ {X : Type} : X → List X → Type where
  head-case : (x : X) (xs : List X) → x ∈ (x :: xs)
  tail-case : (x : X) (xs : List X) → x ∈ xs → (y : X) → x ∈ (y :: xs)
```

Also recall that in [List functions](../List-functions.lagda.md), we defined
`map : {X Y : Type} → (X → Y) → List X → List Y`, which applies a given function
`f : X → Y` to every element of a list `xs : List X`.  We call the resulting
list of type `List Y`, the *`f`-mapped list*.

We want you to formulate the type that describes the notion of *mapped
membership*, relative to the relation `_∈_` and operation `map`.

**Mapped membership** states that:
 > For every list `xs` and function `f`, given any member `x` of `xs`,
   we have that `f(x)` is also a member of the `f`-mapped list.

```agda
mapped-membership : Type → Type → Type
mapped-membership X Y
 = {!!}
```
**Translate** the statement of mapped membership to Agda code.

*Note*: We do not ask you to prove mapped membership.


## Question 5 (Hard 🌶🌶🌶)

A function `f : X → X` is *idempotent* if applying `f` twice yields the same
result as applying `f` once.

**Formalise** the above definition in Agda and **state** and **prove** that if
`f` is idempotent, then so is `map f`.

```agda
is-idempotent : {!!}
is-idempotent = {!!}

map-of-idempotent-function-is-idempotent : {!!}
map-of-idempotent-function-is-idempotent = {!!}
```
