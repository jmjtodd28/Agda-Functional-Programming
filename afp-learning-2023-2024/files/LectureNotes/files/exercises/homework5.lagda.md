# Week 5 - Homework Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.homework5 where


private
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
 map-preserves-length : {A B : Type} (f : A → B) (xs : List A)
                      → length (map f xs) ≡ length xs
 map-preserves-length = {!!}
```

### Exercise 1.2

Another useful fact is that the length of two concatenated lists is the sum of
their respective lengths. **Complete** the proof of this fact.

```agda
 length-of-++ : {A : Type} (xs ys : List A)
              → length (xs ++ ys) ≡ length xs + length ys
 length-of-++ = {!!}
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
 length-of-prefix = {!!}
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
 head = {!!}
```

**Complete** the definition of `head` yourself.

#### Exercise 1.4b

```agda
 length-of-tail : {A : Type} (xs : List A) (p : 1 ≤' length xs)
                → 1 + length (tail xs p) ≡ length xs
 length-of-tail = {!!}
```

**Prove** that the length of a list is obtained by adding 1 to the length of the
tail.

#### Exercise 1.4c

```agda
 ≤'-suc-lemma : (n : ℕ) → n ≤' (1 + n)
 ≤'-suc-lemma = {!!}

 length-of-tail-decreases : {A : Type} (xs : List A) (p : 1 ≤' length xs)
                          → length (tail xs p) ≤' length xs
 length-of-tail-decreases = {!!}
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
   f = {!!}

   g : Y × X → X × Y
   g = {!!}

   gf : g ∘ f ∼ id
   gf = {!!}

   fg : f ∘ g ∼ id
   fg = {!!}

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
   f = {!!}

   g : Y ∔ X → X ∔ Y
   g = {!!}

   gf : g ∘ f ∼ id
   gf = {!!}

   fg : f ∘ g ∼ id
   fg = {!!}

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
   f = {!!}

   g : Σ n ꞉ ℕ , Vector A n → List A
   g = {!!}

   gf : g ∘ f ∼ id
   gf = {!!}

   fg : f ∘ g ∼ id
   fg = {!!}

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
 lfv-preserves-length = {!!}
```

Notice how `bijection` extracts the function `f` you defined in
`lists-from-vectors`.

**Prove** that for any `xs : List A`, the length of `xs` is the same as the
first projection of `f xs : Σ (Vector A)` (where `f : ℕ → List 𝟙` is as you
defined in Exercise 4a).

### Exercise 2.4

```agda
 ≃-refl : (X : Type) → X ≅ X
 ≃-refl X = Isomorphism {!!} {!!}

 ≅-sym : {X Y : Type} → X ≅ Y → Y ≅ X
 ≅-sym (Isomorphism f (Inverse g η ε)) = Isomorphism {!!} (Inverse {!!} {!!} {!!})

 ≅-trans : {X Y Z : Type} → X ≅ Y → Y ≅ Z → X ≅ Z
 ≅-trans (Isomorphism f  (Inverse g  η  ε))
         (Isomorphism f' (Inverse g' η' ε'))
        = Isomorphism (f' ∘ f)
           (Inverse (g ∘ g')
             (λ x → g (g' (f' (f x))) ≡⟨ {!!} ⟩
                    g (f x)           ≡⟨ {!!} ⟩
                    x                 ∎)
             (λ y → f' (f (g (g' y))) ≡⟨ {!!} ⟩
                    f' (g' y)         ≡⟨ {!!} ⟩
                    y                 ∎))
```

## Part 3. Evenness

In the lecture notes, you have seen the predicates `is-even` and `is-odd`:

```agda
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
   subgoal = suc (suc n)       ≡⟨ {!!} ⟩
             suc k + suc k     ≡⟨ {!!} ⟩
             suc ((suc k) + k) ∎

   goal : n ≡ 2 * k
   goal = suc-is-injective (suc-is-injective subgoal)

 evenness-lemma₂ : (n : ℕ) → is-even n → is-even (2 + n)
 evenness-lemma₂ n (k , p) = suc k , goal
  where
   goal : 2 + n ≡ 2 * suc k
   goal = 2 + n         ≡⟨ {!!} ⟩
          2 + (k + k)   ≡⟨ {!!} ⟩
          suc k + suc k ∎
```

**Complete** the above proofs.

### Exercise 3.2

**Prove** that if `is-even n` then `check-even n ≡ true`.

```agda
 even⇒check-even : (n : ℕ) → is-even n → check-even n ≡ true
 even⇒check-even = {!!}
```

**Prove** that if `check-even n ≡ true` then `is-even n`:

```agda
 check-even⇒even : (n : ℕ) → check-even n ≡ true → is-even n
 check-even⇒even = {!!}
```


## Part 4. Commutativity of addition of natural numbers

We wish to prove the commutativity of `_+_` on the natural numbers.

The following proof skeleton has been provided for you, using
[notation for equational reasoning](/files/LectureNotes/files/identity-type.lagda.md#notation-for-equality-reasoning).

```agda
 +-comm : (x y : ℕ) → x + y ≡ y + x
 +-comm 0       0       = {!!}
 +-comm 0       (suc y) = {!!}
 +-comm (suc x) 0       = {!!}
 +-comm (suc x) (suc y)
  = suc (x + suc y)     ≡⟨ {!!} ⟩
    suc (suc (y + x))   ≡⟨ {!!} ⟩
    suc (suc x + y)     ≡⟨ {!!} ⟩
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
 ++-assoc = {!!}
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
   e'' = xs ++ (l ++ l') ≡⟨ {!!} ⟩
         (xs ++ l) ++ l' ≡⟨ {!!} ⟩
         ys ++ l'        ≡⟨ {!!} ⟩
         zs              ∎
```

### Exercise 5.3

**Prove** the following about `≼`.

```agda
 ≼-++ : {X : Type} (xs ys : List X) → xs ≼ (xs ++ ys)
 ≼-++ [] ys        = {!!}
 ≼-++ (x :: xs) ys = {!!}
```

### Exercise 5.4

**Complete** the function below, showing that we can go from `≼'` to `≼`.

*Hint*: Use `≼-++`.

```agda
 ≼-unprime : {X : Type} (xs ys : List X) → xs ≼' ys → xs ≼ ys
 ≼-unprime = {!!}
```

### Exercise 5.5

**Prove** the following facts about `≼'`.

```agda
 ≼'-[] : {X : Type} (xs : List X) → [] ≼' xs
 ≼'-[] = {!!}

 ≼'-cons : {X : Type} (x : X) (xs ys : List X)
         → xs ≼' ys
         → (x :: xs) ≼' (x :: ys)
 ≼'-cons x xs ys (zs , e) = {!!}
```

Note that these amount to the constructors of `≼`.

### Exercise 5.6

**Complete** the function below, showing that we can go from `≼` to `≼'`.

*Hint*: Use `≼'-[]` and `≼'-cons`.

```agda
 ≼-prime : {X : Type} (xs ys : List X) → xs ≼ ys → xs ≼' ys
 ≼-prime = {!!}
```

### Exercise 5.7

Using the functions `≼-unprime` and `≼-prime`, and the fact that `≼'` is
transitive, **prove** that `≼` is transitive too.

```agda
 ≼-is-transitive : {X : Type} (xs ys zs : List X)
                 → xs ≼ ys → ys ≼ zs → xs ≼ zs
 ≼-is-transitive = {!!}
```
