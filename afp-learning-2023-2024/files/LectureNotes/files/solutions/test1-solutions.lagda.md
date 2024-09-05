# Test 1

```agda
{-# OPTIONS --without-K --safe --auto-inline #-}

module solutions.test1-solutions where

open import prelude
open import List-functions
open import natural-numbers-functions
open import Fin
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

## Question 1 - Equalities for Inductive Types

Consider the following ternary data type:

```agda
data 𝟛 : Type where
 bot mid top  : 𝟛
```

**Prove** the following principle:

```agda
principle-of-trivalence : (x : 𝟛) → (x ≡ bot) ∔ (x ≡ mid) ∔ (x ≡ top)
principle-of-trivalence bot = inl (refl bot)
principle-of-trivalence mid = inr (inl (refl mid))
principle-of-trivalence top = inr (inr (refl top))
```

Next, **prove** a similar result for the natural numbers:

```agda
ℕ-equals-zero-or-succ : (x : ℕ) → (x ≡ zero) ∔ (Σ y ꞉ ℕ , x ≡ suc y)
ℕ-equals-zero-or-succ zero = inl (refl zero)
ℕ-equals-zero-or-succ (suc x) = inr (x , refl (suc x))
```

## Question 2 - Adjoining elements to repeated lists

Consider the following function which builds a list of length `n`,
all of whose entries are just a fixed element `a : A`:

```agda
repeat : {A : Type} → ℕ → A → List A
repeat zero a = []
repeat (suc n) a = a :: repeat n a
```
**Show** that adjoining `a` to the front or the back of a list constructed
in this way gives the same result:

```agda
head-or-tail : {A : Type} (n : ℕ) (a : A) → a :: repeat n a ≡ repeat n a ++ [ a ]
head-or-tail zero a = refl _
head-or-tail (suc n) a = ap (λ y → a :: y) (head-or-tail n a)
```
## Question 3 - Products preserve isomorphisms

**Show** that, given bijections `s : A ≅ B` and `t : C ≅ D`, we can produce a bijection `s×t : A × C ≅ B × D`.

**Hint**: You may wish to use `to-×-≡` in sums-equality 

```agda
open import sums-equality
open _≅_
open is-bijection

prod-preserves-isos : ∀ {A B C D} → A ≅ B → C ≅ D → (A × C) ≅ (B × D)
prod-preserves-isos {A} {B} {C} {D} s t = record { bijection = f ; bijectivity = f-is-bijection }
 where
  
  f : A × C → B × D
  f (a , c) = bijection s a , bijection t c

  g : B × D → A × C
  g (b , d) = inverse (bijectivity s) b , inverse (bijectivity t) d

  gf : g ∘ f ∼ id
  gf (a , c) = to-×-≡ (η (bijectivity s) a , η (bijectivity t) c)

  fg : f ∘ g ∼ id
  fg (b , d) = to-×-≡ (ε (bijectivity s) b , ε (bijectivity t) d)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
  
```

## Question 4 - Distributivity of `sum`

Let us write `m ⊗ ns` for the function which multiplies every number in a list `ns : List ℕ` by some
fixed number `m : ℕ`:

```agda
_⊗_ : ℕ → List ℕ → List ℕ
m ⊗ ns = map (m *_) ns
```

**Define** the function `sum` which adds together all the elements of a list of natural numbers (i.e. sum [n₀,...,nₖ] = n₀ + ⋯ + nₖ) :

```agda
sum : List ℕ → ℕ
sum [] = 0
sum (x :: ns) = x + sum ns
```

Now **prove** that multiplication distributes over the `sum` function in the following sense:

```agda
⊗-distrib : (m : ℕ) (ns : List ℕ) → m * (sum ns) ≡ sum (m ⊗ ns)
⊗-distrib m []        = *-comm m 0
⊗-distrib m (n :: ns) =
 m * sum (n :: ns)         ≡⟨ Ⅱ ⟩
 (m * n) + m * (sum ns)    ≡⟨ Ⅰ ⟩
 (m * n) + sum (m ⊗ ns)    ≡⟨ refl _  ⟩
 sum (m * n :: m ⊗ ns)     ≡⟨ refl _  ⟩
 sum (m ⊗ (n :: ns))       ∎
  where
   Ⅰ = sym (ap ((m * n) +_) (sym (⊗-distrib m ns)))
   Ⅱ = *-+-distrib m n (sum ns)
```

## Question 5 - Type Retracts 

Say that a type `Y` is a retract of a type `X` if there are functions `r : X → Y` and `s : Y → X` such that `r (s y) ≡ y` for all `y : Y`.

**Define** the type `retract Y of X` below to consist of the data showing that `Y` is a retract of `X`:

```agda
retract_of_ : Type → Type → Type
retract Y of X = Σ r ꞉ (X → Y) , Σ s ꞉ (Y → X) , r ∘ s ∼ id
```

Now **state and prove** the following fact: if `Y` is a retract of `X` then `List Y` is a retract of `List X`

```agda
retract-List : {X Y : Type} → retract Y of X → retract (List Y) of (List X)
retract-List {X} {Y} (r , s , rs) = R , S , RS
 where
  R : List X → List Y
  R [] = []
  R (x :: xs) = r x :: R xs
  S : List Y → List X
  S [] = []
  S (y :: ys) = s y :: S ys
  RS : R ∘ S ∼ id
  RS [] = refl []
  RS (y :: ys) = r (s y) :: R (S ys) ≡⟨ ap (_:: R (S ys)) (rs y) ⟩
                 y :: R (S ys) ≡⟨ ap (y ::_) (RS ys) ⟩
                 y :: ys ∎

```
