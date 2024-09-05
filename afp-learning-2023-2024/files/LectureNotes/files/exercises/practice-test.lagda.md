# Practice Test

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module exercises.practice-test where

open import prelude
open import natural-numbers-functions
open import List-functions
open import isomorphisms
open import binary-type
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
1. The test starts at 16:00. All students finish at 17:50, with 5% penalty for submissions at 18:00. No submissions are possible after 18:00, so make sure you submit before 18:00.
1. Students with extra time can submit in line with their circumstances. 
1. You must not leave the room between 17:40 and 17:50 to avoid disruption.

## Please check your Canvas submission after you have submitted

This is necessary to make sure you submitted the file you intended to submit. Often students accidentally submit the wrong file.

It is also a good idea to submit to Canvas well before the deadline when you have completed enough questions. We will mark the latest submission.

## Question 1 - Properties of XOR

We define the xor operation (written `⊕`) on binary numbers using the flip function as follow:
```agda
flip : 𝟚 → 𝟚
flip 𝟎 = 𝟏
flip 𝟏 = 𝟎

_⊕_ : 𝟚 → 𝟚 → 𝟚
𝟎 ⊕ c = c
𝟏 ⊕ c = flip c

infixr 40 _⊕_ 
```
Prove that this operation is commutative:

```agda
⊕-comm : (x y : 𝟚) → x ⊕ y ≡ y ⊕ x
⊕-comm x y = {!!}
```
Now **state** the fact `⊕` is associative and prove this as well.

```agda
⊕-assoc : (x y z : 𝟚) → {!!}
⊕-assoc = {!!} 
```

## Question 2 - Parity of doubling 

Let's define the *parity* function (which records the remainder when a
number is divided by 2) on the natural numbers as follows:

```agda
parity : ℕ → 𝟚
parity zero = 𝟎 
parity (suc zero) = 𝟏
parity (suc (suc n)) = parity n
```
Show that `n + n` has `𝟎` parity for any natural number `n`:
```agda
double-has-zero-parity : (n : ℕ) → parity (n + n) ≡ 𝟎
double-has-zero-parity = {!!} 
```

## Question 3 - Products with `Bool`

The cartesian product `×` satisfies the same equations as multiplication of
natural numbers.

For example, remembering that `Bool` has 2 elements, `X × Bool ≅ X ∔ X`.

The type `X × Bool` tags an element `x : X` with either `true` or `false`,
whereas the type `X + X` tags an element `x : X` with either `inl` or `inr`.
In both cases, there are two tags, and thus the types are isomorphic.

**Prove** this isomorphism.

```agda
bool-+-iso : (X : Type) → X × Bool ≅ X ∔ X
bool-+-iso X =
 record { bijection  = f
        ; bijectivity = record { inverse = g ; η = section ; ε = retraction } }
  where
   f : X × Bool → X ∔ X
   f = {!!} 

   g : X ∔ X → X × Bool
   g = {!!} 

   section : g ∘ f ∼ id
   section = {!!}

   retraction : f ∘ g ∼ id
   retraction = {!!} 
```

## Question 4 - Filter commutes with concatenation

Define the `filter` function which keeps only those elements in a list
which satisfy some given boolean-valued predicate.

```agda
filter : {X : Type} (P : X → Bool) → List X → List X
filter = {!!} 
``` 

Now show that filtering a list commutes with concatenation:

```agda
filter-concat : {X : Type} (P : X → Bool) (xs ys : List X) →
  filter P (xs ++ ys) ≡ filter P xs ++ filter P ys
filter-concat = {!!} 
```
**Hint**: You may find it helpful to use `Bool-elim`, the dependent
elimination principle for booleans.

## Question 5 - Fixed points

Given a function `f : X → X`, we say that an element `x : X` is a 
*fixed point* of `f` if `f x = x`. 

**Define** a predicate expressing the fact that a given element `x : X`
is a fixed point of a function `f`.

```agda
is-fixed-point-of : {!!}
is-fixed-point-of = {!!} 
```
Next we define the following membership predicate, giving evidence that
an element `x` appears in a list `xs`:
```agda
_∈_ : {X : Type} → X → List X → Type
x ∈ [] = 𝟘 
x ∈ (y :: xs) = (x ≡ y) ∔ (x ∈ xs)
```
Now, **state** *and* **prove** the following: if every member `x` of
a list `l : List X` is a fixed point of `f`, then `l` is a fixed point
of the function `map f`.

```agda
list-fixed-point : {!!}
list-fixed-point = {!!} 
```

