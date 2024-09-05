# Week 5 - Homework Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module solutions.homework5 where

open import prelude
open import List-functions hiding (++-assoc)
open import natural-numbers-functions hiding (_≤_ ; is-even ; is-odd ; +-comm)
open import isomorphisms
```

## Part 1. Length

In the file [List-functions.lagda.md](../List-functions.lagda.md), the
function `length` is recursively defined as follows.

```agdacode
length : {A : Type} → List A → ℕ
length []        = 0
length (x :: xs) = 1 + length xs
```

In the following exercises we will prove some facts involving the length of
lists. In doing so, you will practise with inductive proofs.

### Exercise 1.1

Recall that we defined `map` as follows (see
[List-functions.lagda.md](../List-functions.lagda.md)).

```agdacode
map : {A B : Type} → (A → B) → List A → List B
map f []        = []
map f (x :: xs) = f x :: map f xs
```

**Prove** that `map` preserves the length of a list.

```agda
{- Verbose solution, manually performing and showing many equalities that hold
   by definition. -}
map-preserves-length : {A B : Type} (f : A → B) (xs : List A)
                     → length (map f xs) ≡ length xs
map-preserves-length f []        = refl 0
map-preserves-length f (x :: xs) =
 length (map f (x :: xs))   ≡⟨ refl _ ⟩
 length (f x :: (map f xs)) ≡⟨ refl _ ⟩
 1 + length (map f xs)      ≡⟨ ap (1 +_) IH ⟩
 1 + length xs              ∎
  where
   IH : length (map f xs) ≡ length xs
   IH = map-preserves-length f xs

{- Alternative, shorter solution that relies on Agda computing the necessary
   equalities for us.
   We come up with such proofs by looking at the goal, using `C-c C-,`, which
   we sometimes normalize (by prefixing the command by `C-u C-u`) to let Agda
   do even more work for us. -}
map-preserves-length' : {A B : Type} (f : A → B) (xs : List A)
                      → length (map f xs) ≡ length xs
map-preserves-length' f []        = refl _
map-preserves-length' f (x :: xs) = ap suc (map-preserves-length' f xs)
```

### Exercise 1.2

Another useful fact is that the length of two concatenated lists is the sum of
their respective lengths. **Complete** the proof of this fact.

```agda
 {- Verbose solution, manually performing and showing many equalities that hold
    by definition. -}
length-of-++ : {A : Type} (xs ys : List A)
             → length (xs ++ ys) ≡ length xs + length ys
length-of-++ []        ys = refl (length ys)
length-of-++ (x :: xs) ys =
  length ((x :: xs) ++ ys)      ≡⟨ refl _ ⟩
  length (x :: (xs ++ ys))      ≡⟨ refl _ ⟩
  (1 + length (xs ++ ys))       ≡⟨ ap (1 +_) IH ⟩
  (1 + (length xs + length ys)) ≡⟨ +-assoc 1 (length xs) (length ys) ⟩
  (1 + length xs) + length ys   ≡⟨ refl _ ⟩
  length (x :: xs) + length ys  ∎
 where
   IH : length (xs ++ ys) ≡ length xs + length ys
   IH = length-of-++ xs ys

 {- Alternative, shorter solution that relies on Agda computing the necessary
    equalities for us.
    We come up with such proofs by looking at the goal, using `C-c C-,`, which
    we sometimes normalize (by prefixing the command by `C-u C-u`) to let Agda
    do even more work for us. -}
length-of-++' : {A : Type} (xs ys : List A)
              → length (xs ++ ys) ≡ length xs + length ys
length-of-++' []        ys = refl (length ys)
length-of-++' (x :: xs) ys = ap suc IH
  where
   IH : length (xs ++ ys) ≡ length xs + length ys
   IH = length-of-++ xs ys
```

### Exercise 1.3

Recall `≤'` from Lab Sheet 4:

```agda
_≤'_ : ℕ → ℕ → Type
x ≤' y = Σ k ꞉ ℕ , x + k ≡ y
```

Similarly, we now define a list-prefix relation as follows:

```agda
_≼'_ : {X : Type} → List X → List X → Type
_≼'_ {X} xs ys = Σ zs ꞉ List X , xs ++ zs ≡ ys
```

**Prove** that the length of a prefix of a list `ys` is less than the length of
`ys`, relating the two notions above.

```agda
length-of-prefix : {A : Type} (xs ys : List A)
                 → xs ≼' ys
                 → length xs ≤' length ys
length-of-prefix xs ys (zs , e) = (length zs , goal)
 where
  goal = length xs + length zs ≡⟨ sym (length-of-++ xs zs) ⟩
         length (xs ++ zs)     ≡⟨ ap length e              ⟩
         length ys             ∎
```

### Exercise 1.4

A nice use case of the length function is that we are now able to define safe
`head` and `tail` operations on nonempty lists.

We say that a list is *nonempty* if its length is at least 1.
```agda
is-nonempty : {A : Type} → List A → Type
is-nonempty xs = 1 ≤' length xs
```

We can then define `tail` as follows.
```agda
tail : {A : Type} (xs : List A) → is-nonempty xs → List A
tail (x :: xs) p = xs
```

Agda accepts this definition and does not complain about missing the `[]`-case,
because it realizes that `[]` does not satisfy `is-nonempty`.

#### Exercise 1.4a

```agda
head : {A : Type} (xs : List A) → is-nonempty xs → A
head (x :: xs) p = x
```

**Complete** the definition of `head` yourself.

#### Exercise 1.4b

```agda
length-of-tail : {A : Type} (xs : List A) (p : 1 ≤' length xs)
               → 1 + length (tail xs p) ≡ length xs
length-of-tail (x :: xs) p =
 1 + length (tail (x :: xs) p) ≡⟨ refl _ ⟩
 1 + length xs                 ≡⟨ refl _ ⟩
 length (x :: xs)              ∎
```

**Prove** that the length of a list is obtained by adding 1 to the length of the
tail.

#### Exercise 1.4c

```agda
≤'-suc-lemma : (n : ℕ) → n ≤' (1 + n)
≤'-suc-lemma zero    = (1 , refl 1)
≤'-suc-lemma (suc n) = (1 , ap suc goal)
 where
  goal : n + 1 ≡ suc n
  goal = n + 1       ≡⟨ +-step n zero ⟩
         suc (n + 0) ≡⟨ +-base (suc n) ⟩
         suc n       ∎

length-of-tail-decreases : {A : Type} (xs : List A) (p : 1 ≤' length xs)
                         → length (tail xs p) ≤' length xs
length-of-tail-decreases (x :: xs) p = goal
 where
  goal : length xs ≤' (1 + length xs)
  goal = ≤'-suc-lemma (length xs)
```

**Complete** the proof of the following lemma and use it to prove that the
length of the tail of a list is less than the length of the full list.

## Part 2. Isomorphisms

Make sure you have read the [file on isomorphisms](../isomorphisms.lagda.md),
where we define ismorphisms and show that `Bool ≅ 𝟚`.

You will now give three more isomorphisms. In each case, you should think
about *why* and *how* each pair of types are isomorphic before attemping to
formalise the isomorphism.

### Exercise 2.1

```agda
×-iso : (X Y : Type) → X × Y ≅ Y × X
×-iso X Y = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : X × Y → Y × X
  f (x , y) = y , x

  g : Y × X → X × Y
  g (y , x) = x , y

  gf : g ∘ f ∼ id
  gf (x , y) = refl (x , y)

  fg : f ∘ g ∼ id
  fg (y , x) = refl (y , x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

**Show** that X × Y is isomorphic to Y × X using the above template.

### Exercise 2.2

```agda
+-iso : (X Y : Type) → X ∔ Y ≅ Y ∔ X
+-iso X Y = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : X ∔ Y → Y ∔ X
  f (inl x) = inr x
  f (inr y) = inl y

  g : Y ∔ X → X ∔ Y
  g (inl y) = inr y
  g (inr x) = inl x

  gf : g ∘ f ∼ id
  gf (inl x) = refl (inl x)
  gf (inr y) = refl (inr y)

  fg : f ∘ g ∼ id
  fg (inl y) = refl (inl y)
  fg (inr x) = refl (inr x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

### Exercise 2.3

```agda
lists-from-vectors : {A : Type} → List A ≅ (Σ n ꞉ ℕ , Vector A n)
lists-from-vectors {A}
 = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : List A → Σ n ꞉ ℕ , Vector A n
  f []        = 0 , []
  f (x :: xs) = suc (fst (f xs)) , (x :: snd (f xs))

  g : Σ n ꞉ ℕ , Vector A n → List A
  g (0     , []       ) = []
  g (suc n , (x :: xs)) = x :: g (n , xs)

  gf : g ∘ f ∼ id
  gf []        = refl []
  gf (x :: xs) = ap (x ::_) (gf xs)

  fg : f ∘ g ∼ id
  fg (0     , []       ) = refl (0 , [])
  fg (suc n , (x :: xs)) =
   ap (λ - → suc (fst -) , (x :: snd -)) (fg (n , xs))

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

**Show** that the the type `List A` is isomorphic to the type `Σ (Vector A)`.

(Note that this is the first question in [this question
sheet](../vector-and-list-isomorphisms.lagda.md)).

Hint: The statement of Exercise 2.3b may help you.

### Exercise 2.3b

```agda
open _≅_

lfv-preserves-length : {A : Type} (xs : List A)
                     → fst (bijection lists-from-vectors xs)
                     ≡ length xs
lfv-preserves-length []        = refl 0
lfv-preserves-length (x :: xs) = ap suc (lfv-preserves-length xs)
```

Notice how `bijection` extracts the function `f` you defined in
`lists-from-vectors`.

**Prove** that for any `xs : List A`, the length of `xs` is the same as the
first projection of `f xs : Σ (Vector A)` (where `f : ℕ → List 𝟙` is as you
defined in Exercise 4a).

### Exercise 2.4

```agda
≃-refl : (X : Type) → X ≅ X
≃-refl X = Isomorphism (λ z → z) (Inverse (λ z → z) refl refl)

≅-sym : {X Y : Type} → X ≅ Y → Y ≅ X
≅-sym (Isomorphism f (Inverse g η ε)) = Isomorphism g (Inverse f ε η)

≅-trans : {X Y Z : Type} → X ≅ Y → Y ≅ Z → X ≅ Z
≅-trans (Isomorphism f  (Inverse g  η  ε))
        (Isomorphism f' (Inverse g' η' ε'))
       = Isomorphism (f' ∘ f)
          (Inverse (g ∘ g')
            (λ x → g (g' (f' (f x))) ≡⟨ ap g (η' (f x)) ⟩
                   g (f x)           ≡⟨ η x ⟩
                   x                 ∎)
            (λ y → f' (f (g (g' y))) ≡⟨ ap f' (ε (g' y)) ⟩
                   f' (g' y)         ≡⟨ ε' y ⟩
                   y                 ∎))
```

## Part 3. Evenness

In the lecture notes, you have seen the predicates `is-even` and `is-odd`:

```agda
module _ where -- was private
 is-even is-odd : ℕ → Type
 is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
 is-odd  x = Σ y ꞉ ℕ , x ≡ 1 + 2 * y
```

In these exercises, we will define a Boolean-valued version of the `is-even`
predicate and prove that the two versions are _logically_ equivalent:

```agda
check-even : ℕ → Bool
check-even zero          = true
check-even (suc zero)    = false
check-even (suc (suc n)) = check-even n
```

### Exercise 3.1

First, we will have to prove two lemmas that we will use in Exercise 3.2, where
we will prove our main result.

```agda
evenness-lemma₁ : (n : ℕ) → is-even (2 + n) → is-even n
evenness-lemma₁ n (suc k , p) = k , goal
 where
  subgoal : suc (suc n) ≡ suc (suc (2 * k))
  subgoal = suc (suc n)       ≡⟨ p ⟩
            suc k + suc k     ≡⟨ ap suc (+-step k k) ⟩
            suc ((suc k) + k) ∎

  goal : n ≡ 2 * k
  goal = suc-is-injective (suc-is-injective subgoal)

evenness-lemma₂ : (n : ℕ) → is-even n → is-even (2 + n)
evenness-lemma₂ n (k , p) = suc k , goal
 where
  goal : 2 + n ≡ 2 * suc k
  goal = 2 + n         ≡⟨ ap (2 +_) p ⟩
         2 + (k + k)   ≡⟨ ap suc (sym (+-step k k)) ⟩
         suc k + suc k ∎
```

**Complete** the above proofs.

### Exercise 3.2

**Prove** that if `is-even n` then `check-even n ≡ true`.

```agda
even⇒check-even : (n : ℕ) → is-even n → check-even n ≡ true
even⇒check-even zero _ = refl true
even⇒check-even (suc zero) (suc zero , ())
even⇒check-even (suc zero) (suc (suc _) , ())
even⇒check-even (suc (suc n)) p = even⇒check-even n (evenness-lemma₁ n p)
```

**Prove** that if `check-even n ≡ true` then `is-even n`:

```agda
check-even⇒even : (n : ℕ) → check-even n ≡ true → is-even n
check-even⇒even zero (refl true) = zero , refl zero
check-even⇒even (suc zero) ()
check-even⇒even (suc (suc n)) p = evenness-lemma₂ n (check-even⇒even n p)
```


## Part 4. Commutativity of addition of natural numbers

We wish to prove the commutativity of `_+_` on the natural numbers.

The following proof skeleton has been provided for you, using
[notation for equational reasoning](/files/LectureNotes/files/identity-type.lagda.md#notation-for-equality-reasoning).

```agda
+-comm : (x y : ℕ) → x + y ≡ y + x
+-comm 0       0       = refl zero
+-comm 0       (suc y) =  ap  suc        (+-comm zero y)
+-comm (suc x) 0       =  ap  suc        (+-comm x zero)
+-comm (suc x) (suc y)
 = suc (x + suc y)     ≡⟨ ap  suc        (+-comm x (suc y)) ⟩
   suc (suc (y + x))   ≡⟨ ap (suc ∘ suc) (+-comm y x)       ⟩
   suc (suc x + y)     ≡⟨ ap  suc        (+-comm (suc x) y) ⟩
   suc (y + suc x)     ∎
```

**Fill** the holes of our proof that `_+_` is commutative.

HINT. You may wish to use functions defined in the handouts *and* in the previous exercises to make your life easier.

## Part 5. Prefixes of lists

In this part we will study two ways of expressing that a list is prefix of
another list.

This will be similar to how we had two ways of expressing less-than-or-equal
`≤` on natural numbers, as seen in the Lab Sheet for Week 4. In particular,
you will notice how to the structure of the proofs below mirror the structure
of the proofs in this week's Lab Sheet.

The first definition given above uses a `Σ`-type and was given above:

```agdacode
 _≼'_ : {X : Type} → List X → List X → Type
 _≼'_ {X} xs ys = Σ zs ꞉ List X , xs ++ zs ≡ ys
```

The first definition is an inductive one.

```agda
data _≼_ {X : Type} : List X → List X → Type where
 []-is-prefix : (xs : List X) → [] ≼ xs
 ::-is-prefix : (x : X) (xs ys : List X)
              → xs ≼ ys → (x :: xs) ≼ (x :: ys)
```

It says:
1. that the empty list is a prefix of any list;
1. if `xs` is a prefix of `ys`, then `x :: xs` is a prefix of `x :: ys`.

The second item says that you can extend prefixes by adding the same element at
the start.


It says that `xs` is a prefix of `ys` if we have another list `zs` such that
`xs ++ zs ≡ ys`. In other words, `xs` can be extended to `ys.`

### Examples

Here are some examples of prefixes of lists.

```agda
≼'-example₀ : [] ≼' (1 :: 2 :: [ 3 ])
≼'-example₀ = ((1 :: 2 :: [ 3 ]) , refl (1 :: 2 :: [ 3 ]))

≼'-example₁ : [ 1 ] ≼' (1 :: [ 2 ])
≼'-example₁ = ([ 2 ] , refl (1 :: [ 2 ]))

≼'-example₂ : (7 :: [ 3 ]) ≼' (7 :: 3 :: 4 :: [ 9 ])
≼'-example₂ = ((4 :: [ 9 ]) , refl (7 :: 3 :: 4 :: [ 9 ]))
```

For comparison, here are some examples using `≼` instead of `≼'`.

```agda
≼-example₀ : [] ≼ (1 :: 2 :: [ 3 ])
≼-example₀ = []-is-prefix (1 :: 2 :: [ 3 ])

≼-example₁ : [ 1 ] ≼ (1 :: [ 2 ])
≼-example₁ = ::-is-prefix 1 [] [ 2 ]
                          ([]-is-prefix [ 2 ])

≼-example₂ : (7 :: [ 3 ]) ≼ (7 :: 3 :: 4 :: [ 9 ])
≼-example₂ = ::-is-prefix 7 [ 3 ] (3 :: 4 :: [ 9 ])
                          (::-is-prefix 3 [] (4 :: [ 9 ])
                                          ([]-is-prefix (4 :: [ 9 ])))
```

Notice how we build up the proofs by consecutive uses of `::-is-prefix`,
finishing with `[]-is-prefix`. This reflects the inductive definition of `≼`.

We will prove that `x ≼ y` and `x ≼' y` are logically equivalent, but first we
include a useful exercise on associativity.

### Exercise 5.1

**Prove** that concatenation of lists, `++`, is associative.

```agda
++-assoc : {X : Type} (xs ys zs : List X)
         → (xs ++ ys) ++ zs ≡ xs ++ (ys ++ zs)
++-assoc []        ys zs = refl (ys ++ zs)
++-assoc (x :: xs) ys zs = ap (x ::_) (++-assoc' xs ys zs)
```

### Exercise 5.2

**Complete** the holes in the equational reasoning below to prove that `≼'` is
transitive.

```agda
≼'-is-transitive : {X : Type} (xs ys zs : List X)
                 → xs ≼' ys → ys ≼' zs → xs ≼' zs
≼'-is-transitive xs ys zs (l , e) (l' , e') = ((l ++ l') , e'')
 where
  e'' : xs ++ l ++ l' ≡ zs
  e'' = xs ++ (l ++ l') ≡⟨ sym (++-assoc xs l l') ⟩
        (xs ++ l) ++ l' ≡⟨ ap (_++ l') e ⟩
        ys ++ l'        ≡⟨ e' ⟩
        zs              ∎
```

### Exercise 5.3

**Prove** the following about `≼`.

```agda
≼-++ : {X : Type} (xs ys : List X) → xs ≼ (xs ++ ys)
≼-++ [] ys        = []-is-prefix ys
≼-++ (x :: xs) ys = ::-is-prefix x xs (xs ++ ys) (≼-++ xs ys)
```

### Exercise 5.4

**Complete** the function below, showing that we can go from `≼'` to `≼`.

*Hint*: Use `≼-++`.

```agda
≼-unprime : {X : Type} (xs ys : List X) → xs ≼' ys → xs ≼ ys
≼-unprime xs ys (zs , h) = transport (xs ≼_) h (≼-++ xs zs)
```

### Exercise 5.5

**Prove** the following facts about `≼'`.

```agda
≼'-[] : {X : Type} (xs : List X) → [] ≼' xs
≼'-[] xs = xs , refl xs

≼'-cons : {X : Type} (x : X) (xs ys : List X)
        → xs ≼' ys
        → (x :: xs) ≼' (x :: ys)
≼'-cons x xs ys (zs , e) = zs , ap (x ::_) e
```

Note that these amount to the constructors of `≼`.

### Exercise 5.6

**Complete** the function below, showing that we can go from `≼` to `≼'`.

*Hint*: Use `≼'-[]` and `≼'-cons`.

```agda
≼-prime : {X : Type} (xs ys : List X) → xs ≼ ys → xs ≼' ys
≼-prime []        ys        ([]-is-prefix .ys)       = ≼'-[] ys
≼-prime (x :: xs) (x :: ys) (::-is-prefix x xs ys h) = ≼'-cons x xs ys (≼-prime xs ys h)
```

### Exercise 5.7

Using the functions `≼-unprime` and `≼-prime`, and the fact that `≼'` is
transitive, **prove** that `≼` is transitive too.

```agda
≼-is-transitive : {X : Type} (xs ys zs : List X)
                → xs ≼ ys → ys ≼ zs → xs ≼ zs
≼-is-transitive xs ys zs h1 h2 =
 ≼-unprime xs zs (≼'-is-transitive xs ys zs (≼-prime xs ys h1) (≼-prime ys zs h2))
```
