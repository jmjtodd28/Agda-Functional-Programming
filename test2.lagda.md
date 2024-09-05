# Test 2

```agda
module test2 where

open import prelude
open import natural-numbers-type
open import natural-numbers-functions hiding (max)
open import Bool
open import List
open import List-functions
open import isomorphisms
open import strict-total-order
open import Fin
open import binary-type
open import decidability
open _≅_

open import solutions.lab2 using (max ; max-commutative)

```

## Important instructions
1. **Copy this file** (`test2-template.lagda.md`) to a new file `test2.lagda.md` in the same directory, and work in that copy.
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
1. The test starts at 16:00. The test ends at 17:50, with 5% penalty for submissions at 17:59. No submissions are possible after 17:59, so make sure you submit before 18:00. Students with extra time will be able see their deadlines, with and without penalty, on Canvas.
1. You must not leave the room between 17:40 and 17:50 to avoid disruption.

## Please check your Canvas submission after you have submitted

This is necessary to make sure you submitted the file you intended to submit. Often students accidentally submit the **wrong file**.

It is also a good idea to submit to Canvas well before the deadline when you have completed enough questions. We will mark the latest submission.

## Question 1

Consider the type of binary trees.

```agda
data T (X : Type) : Type where
  lf : T X
  nd : X → T X → T X → T X
```

**Task 1.1.** The `size` of a binary tree is the number of nodes it contains.  Implement this function:
```agda
size : {X : Type} → T X → ℕ
size lf = zero
size (nd x l r) = 1 + (size l) + (size r)
```
Additionally, we have the pre-order traversal which produces the list of nodes from the tree:
```agda
flatten : {X : Type} → T X → List X
flatten lf = []
flatten (nd x l r) = x :: flatten l ++ flatten r
```
Recall that the length of the concatenation of two lists is the sum of their lengths:
```agda
length-++ : {X : Type} (xs ys : List X) → length xs + length ys ≡ length (xs ++ ys)
length-++ [] ys = refl _
length-++ (x :: xs) ys = ap suc (length-++ xs ys)
```
**Task 1.2.** Show that the size of a tree is the same as the length of its flattening.
```agda
flatten-size : {X : Type} (t : T X) → size t ≡ length (flatten t)
flatten-size lf = refl 0
flatten-size (nd x l r) =
 suc (size l + size r)                         ≡⟨ ap (λ t → (suc (t + size r))) (flatten-size l) ⟩
 suc (length (flatten l) + size r)             ≡⟨ ap (λ t → suc (length (flatten l) + t )) (flatten-size r) ⟩
 suc (length (flatten l) + length (flatten r)) ≡⟨ ap suc (length-++ (flatten l) (flatten r)) ⟩
 suc (length (flatten l ++ flatten r))         ∎

```

-- suc (size l + size r) ≡ suc (length (flatten l ++ flatten r))

**Hint.** A possible solution uses `ap₂` and the provided lemma `length-++`.

## Question 2

**Task 2.1.** Define the height of a binary tree as the length of its longest branch.
```agda
height : {A : Type} → T A → ℕ
height lf = zero
height (nd x l r) = 1 + max (height l) (height r)
```
Now recall that the `mirror` function is defined by recursively swapping the left and right branches:
```agda
mirror : {A : Type} → T A → T A
mirror lf = lf
mirror (nd x l r) = nd x (mirror r) (mirror l)
```
**Task 2.2.** Show that the height of a tree and its mirror are the same:
```agda
height-of-mirror : {A : Type} (t : T A) → height (mirror t) ≡ height t
height-of-mirror lf = refl zero
height-of-mirror (nd x l r) = 
 suc (max (height (mirror r)) (height (mirror l))) ≡⟨ ap (λ t → suc (max (height (mirror r)) t)) (height-of-mirror l) ⟩
 suc (max (height (mirror r)) (height l))          ≡⟨ ap (λ t → suc (max t (height l))) (height-of-mirror r) ⟩
 suc (max (height r) (height l))                   ≡⟨ ap suc (max-commutative (height r) (height l)) ⟩
 suc (max (height l) (height r))                   ∎

```

**Hint.** You may wish to use `max-commutative` and `ap₂`.

## Question 3

We can define the type of positions in a binary tree as follows:

```agda
BinPos : {X : Type} → T X → Type
BinPos lf = 𝟘
BinPos (nd x l r) = 𝟙 ∔ BinPos l ∔ BinPos r

fetch : {X : Type} (t : T X) → BinPos t → X
fetch (nd x l r) (inl ⋆) = x
fetch (nd x l r) (inr (inl lp)) = fetch l lp
fetch (nd x l r) (inr (inr rp)) = fetch r rp
```
**Task 3.1.** Show that every position of a tree gives rise to a position of its mirror:
```agda
mirror-pos : {X : Type} (t : T X) → BinPos t → BinPos (mirror t)
mirror-pos (nd x l r) (inl y)       = inl ⋆
mirror-pos (nd x l r) (inr (inl y)) = inr (inr (mirror-pos l y))
mirror-pos (nd x l r) (inr (inr y)) = inr (inl (mirror-pos r y))
```
**Task 3.2.** Show that the element in a tree at a given position is the same as
the element in the mirrored tree at the mirrored position.
```
mirror-fetch : {X : Type} (t : T X) (p : BinPos t)
             → fetch t p ≡ fetch (mirror t) (mirror-pos t p)
mirror-fetch (nd x l r) (inl ⋆)       = refl x
mirror-fetch (nd x l r) (inr (inl y)) = mirror-fetch l y
mirror-fetch (nd x l r) (inr (inr y)) = mirror-fetch r y
```

## Question 4

We define `foldr` and `foldl` as follows.
```agda
foldl : {X Y : Type} → (Y → X → Y) → Y → List X → Y
foldl f u []        = u
foldl f u (x :: xs) = f (foldl f u xs) x

foldr : {X Y : Type} → (X → Y → Y) → Y → List X → Y
foldr f u []        = u
foldr f u (x :: xs) = f x (foldr f u xs)
```
The following two examples illustrate the different ways that `foldl`
and `foldr` apply the given function to a list:
```agda
example-l : (x y z w : ℕ) → foldl max w (x :: y :: z :: []) ≡ max (max (max w z) y) x
example-l x y z w = refl _

example-r : (x y z w : ℕ) → foldr max w (x :: y :: z :: []) ≡ max x (max y (max z w))
example-r x y z w = refl _
```

**Task 4.1.** A function `f : A → A → A` is said to be commutative if `f x y ≡ f y x`. Define this in Agda.
```agda
is-commutative : {X : Type} (f : X → X → X) → Type
is-commutative {X} f = (x y : X) → f x y ≡ f y x
```

**Task 4.2.** Show that, if the given function `f` is commutative, then `foldr` and
`foldl` give the same result:
```agda
commutative-implies-foldr-coincides-with-foldl
 : {X : Type}
 → (f : X → X → X)
 → is-commutative f
 → (x : X) (xs : List X)
 → foldr f x xs ≡ foldl f x xs
commutative-implies-foldr-coincides-with-foldl f cf x [] = refl x
commutative-implies-foldr-coincides-with-foldl f cf x (y :: xs) =
 f y (foldr f x xs) ≡⟨ ap (f y) (commutative-implies-foldr-coincides-with-foldl f cf x xs) ⟩
 f y (foldl f x xs) ≡⟨ cf y (foldl f x xs) ⟩
 f (foldl f x xs) y ∎

```

## Question 5

A **permutation** is defined as an isomorphism of the type `Fin n` with itself.

```agda
Permutation : ℕ → Type
Permutation n = Fin n ≅ Fin n
```

In this question, we are going to define the `sign` of such a
permutation.  To do so, first recall that the type `Fin n` carries a
natural total order, and that this order is decidable:

```agda
_<[Fin]_ : {n : ℕ} → Fin n → Fin n → Type
zero <[Fin] zero = 𝟘
zero <[Fin] suc q = 𝟙
suc p <[Fin] zero = 𝟘
suc p <[Fin] suc q = p <[Fin] q

<[Fin]-decidable : {n : ℕ} → (p : Fin n) → (q : Fin n) → is-decidable (p <[Fin] q)
<[Fin]-decidable zero zero = 𝟘-is-decidable
<[Fin]-decidable zero (suc _) = 𝟙-is-decidable
<[Fin]-decidable (suc _) zero = 𝟘-is-decidable
<[Fin]-decidable (suc p) (suc q) = <[Fin]-decidable p q
```

With this in mind, the `sign` of a permutation can be defined as the
*parity of the number of pairs which are transposed with respect to
this order*.

Here is an example with `n = 5`, with the permutation `f` indicated as a table for convenience.
```notagda
    i | 0 1 2 3 4
  ----+----------
  f i | 4 2 1 3 0
```
Now consider, looking at the bottom row of the above table, the following pairs:
```notagda
   (4 , 2) (4 , 1) (4 , 3) (4 , 0) -- We have 4 transpositions.
           (2 , 1) (2 , 3) (2 , 0) -- We have 2 transpositions.
                   (1 , 3) (1 , 0) -- We have 1 transposition.
                           (3 , 0) -- We have 1 transposition.
```
These are the pairs `(f i , f j)` with `i < j`. Such a pair is a called a transposition if `¬(f i < f j)`.
We indicate the transpositions with square brackets:
```notagda
   [4 , 2] [4 , 1] [4 , 3] [4 , 0]
           [2 , 1] (2 , 3) [2 , 0]
                   (1 , 3) [1 , 0]
                           [3 , 0]
```
So in this example there are only two pairs which are not transposed.
Because the number of transposed pairs is `8`, which is even, the parity is `𝟎 : 𝟚`.

**Task.** Define a function that computes the sign of a permutation.
```
sign : (n : ℕ) → Permutation n → 𝟚
sign zero (Isomorphism bijection₁ (Inverse inverse η ε)) = {!η !}
sign (suc n) (Isomorphism bijection₁ bijectivity₁) = {!!}
```

The above example of a permutation can be coded in Agda as follows, and you
may wish to use it for testing. Notice that f is its own inverse.
```agda
𝕗 : Permutation 5
𝕗 = Isomorphism f (Inverse f ff ff)
 where
  f : Fin 5 → Fin 5
  f zero = suc (suc (suc (suc zero)))
  f (suc zero) = suc (suc zero)
  f (suc (suc zero)) = suc zero
  f (suc (suc (suc zero))) = suc (suc (suc zero))
  f (suc (suc (suc (suc zero)))) = zero

  ff : f ∘ f ∼ id
  ff zero = refl _
  ff (suc zero) = refl _
  ff (suc (suc zero)) = refl _
  ff (suc (suc (suc zero))) = refl _
  ff (suc (suc (suc (suc zero)))) = refl _
```

**Hint** : Try to enumerate the pairs of elements of `Fin n` and count the number of transpositions.
