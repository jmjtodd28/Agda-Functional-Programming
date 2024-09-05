# Week 6 - Homework Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module solutions.homework6 where

private
 open import prelude hiding (Bool-elim; _∘_; id)
 open import natural-numbers-functions hiding (_≤_ ; is-even ; +-assoc; +-comm)
 open import List-functions
 open import isomorphisms
 open import negation
```
We will also want to use some things from the Lab of Week 4:

```agda
 open import solutions.lab4 hiding (_≤_; ≤-trans; +-assoc)
 open import solutions.homework5 hiding (is-even)
```

## Part I: More on length

Besides `map`, the function `reverse` is another example of a length-preserving
operation.

```agda
 length-of-reverse : {A : Type} (xs : List A)
                   → length (reverse xs) ≡ length xs
 length-of-reverse []        = refl 0
 length-of-reverse (x :: xs) =
   length (reverse xs ++ [ x ])       ≡⟨ length-of-++ (reverse xs) [ x ] ⟩
   length (reverse xs) + length [ x ] ≡⟨ refl _                          ⟩
   length (reverse xs) + 1            ≡⟨ ap (_+ 1) IH                    ⟩
   length xs + 1                      ≡⟨ +-comm (length xs) 1            ⟩
   1 + length xs                      ∎
    where
     IH : length (reverse xs) ≡ length xs
     IH = length-of-reverse xs
```

**Prove** the above.

## Part II: More on isomorphisms

### Exercise 2a

```agda
 ℕ-[⋆]-iso : ℕ ≅ List 𝟙
 ℕ-[⋆]-iso = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : ℕ → List 𝟙
   f 0       = []
   f (suc n) = ⋆ :: f n

   g : List 𝟙 → ℕ
   g []        = 0
   g (⋆ :: ⋆s) = suc (g ⋆s)

   gf : g ∘ f ∼ id
   gf 0       = refl 0
   gf (suc n) = ap suc (gf n)

   fg : f ∘ g ∼ id
   fg [] = refl []
   fg (⋆ :: ⋆s) = ap (⋆ ::_) (fg ⋆s)

   f-is-bijection : is-bijection f
   f-is-bijection = record { inverse = g ; η = gf ; ε = fg }
```

**Show** that the type of natural numbers `ℕ` is isomorphic to the type of lists
over the unit type `𝟙`.

Hint: The statement of Exercise 2b may help you.

### Exercise 2b

```agda
 open _≅_

 ℕ→[⋆]-preserves-length : (n : ℕ) → length (bijection ℕ-[⋆]-iso n) ≡ n
 ℕ→[⋆]-preserves-length zero = refl 0
 ℕ→[⋆]-preserves-length (suc n) = ap suc (ℕ→[⋆]-preserves-length n)
```

Notice how `bijection` extracts the function `f` you defined in `ℕ-[⋆]-iso`.

**Prove** that for any `n : ℕ`, the length of the list `f n : List 𝟙`
(where `f : ℕ → List 𝟙` is as you defined in Exercise 3a) is `n`.

## Part III: More on evenness

In this exercise, we will continue where we left off in the lab exercises on
evenness. Recall the predicates `is-even` and `check-even`:

```agda
 is-even : ℕ → Type
 is-even x = Σ y ꞉ ℕ , x ≡ 2 * y
```

Now recall the discussion about decidable predicates that we had in the previous
weeks. When you proved that `check-even` and `is-even` are logically equivalent
in the lab, you have in fact implicitly proved that `is-even` is a decidable
predicate! In this exercise, we will make this implicit proof _explicit_.

**Complete** the remaining holes in the following proof outline; starting with
proving a lemma stating that a Boolean is either `true` or `false`.

```agda
 principle-of-bivalence : (b : Bool) → (b ≡ true) ∔ (b ≡ false)
 principle-of-bivalence true  = inl (refl true)
 principle-of-bivalence false = inr (refl false)

 is-even-is-decidable : (n : ℕ) → is-decidable (is-even n)
 is-even-is-decidable n =
  ∔-nondep-elim goal₁ goal₂ (principle-of-bivalence (check-even n))
   where
    goal₁ : check-even n ≡ true → is-decidable (is-even n)
    goal₁ p = inl (check-even⇒even n p)

    goal₂ : check-even n ≡ false → is-decidable (is-even n)
    goal₂ p = inr subgoal
     where
      subgoal : ¬ is-even n
      subgoal q = true-is-not-false
                   (true        ≡⟨ sym (even⇒check-even n q) ⟩
                   check-even n ≡⟨ p ⟩
                   false        ∎)
```

## Part IV: Stretcher exercises on length

*The following two exercises are rather hard and are should be interesting to
students that like a challenge.*

Recall that we can define `filter` as
```agda
 filter : {A : Type} → (A → Bool) → List A → List A
 filter P []        = []
 filter P (x :: xs) = if P x then (x :: ys) else ys
  where
   ys = filter P xs
```

We also remind you of the inductively defined less-than-or-equal relation `≤`
on the natural numbers.

```agda
 data _≤_ : ℕ → ℕ → Type where
   ≤-zero : (  y : ℕ) → 0 ≤ y
   ≤-suc  : (x y : ℕ) → x ≤ y → suc x ≤ suc y
```

Finally, the following lemmas are provided to you for your convenience.

```agda
 ≤-suc-lemma : (n : ℕ) → n ≤ (1 + n)
 ≤-suc-lemma 0       = ≤-zero (1 + 0)
 ≤-suc-lemma (suc n) = goal
  where
   IH : n ≤ (1 + n)
   IH = ≤-suc-lemma n
   goal : suc n ≤ suc (suc n)
   goal = ≤-suc n (suc n) IH

 Bool-elim : (A : Bool → Type)
           → A false
           → A true
           → (x : Bool) → A x
 Bool-elim A x₀ x₁ false = x₀
 Bool-elim A x₀ x₁ true  = x₁
```

### Exercise 4a (stretcher 🌶)

**Prove** that filtering a list decreases its length.

```agda
 ≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
 ≤-trans zero y z p q
  = ≤-zero z
 ≤-trans (suc x) .(suc y) .(suc z) (≤-suc .x y p) (≤-suc .y z q)
  = ≤-suc x z (≤-trans x y z p q)

+-assoc : (x y z : ℕ) → (x + y) + z ≡ x + (y + z)
+-assoc 0       y z = refl (y + z)
+-assoc (suc x) y z =
   (suc x + y) + z   ≡⟨ refl _ ⟩
   suc (x + y) + z   ≡⟨ refl _ ⟩
   suc ((x + y) + z) ≡⟨ ap suc (+-assoc x y z) ⟩
   suc (x + (y + z)) ≡⟨ refl _ ⟩
   suc x + (y + z)   ∎
```

*Hints*:
 - You can use `≤-trans` from the [sample solutions to
   Lab 4](lab4-solutions.lagda.md) if you need that `≤` is transitive.
   (The sample solutions are already imported for you.)
 - Think about how to use `Bool-elim`.

### Exercise 4b (stretcher 🌶🌶)

Given a predicate `P : A → Bool` and a list `xs : List A`, we could filter `xs`
by `P` and by `not ∘ P`. If we do this and compute the lengths of the resulting
lists, then we expect their sum to be equal to the length of the unfiltered list
`xs`. **Prove** this fact.

```agda
length-of-filter : {A : Type} (P : A → Bool) (xs : List A)
                 → length (filter P xs) ≤ length xs
length-of-filter P []        = ≤-zero 0
length-of-filter P (x :: xs) = Bool-elim goal-statement false-case
                                                          true-case
                                                          (P x)
  where
   ys = filter P xs

   {- Note that by definition
        filter P (x :: xs) = if P x then (x :: ys) else ys
      and so goal-statement is almost
        length (filter P (x :: xs)) ≤ length (x :: xs)
      except that we replace "P x" by the Boolean "b". -}
   goal-statement : Bool → Type
   goal-statement b = length (if b then (x :: ys) else ys) ≤ length (x :: xs)

   IH : length ys ≤ length xs
   IH = length-of-filter P xs

   {- The type of "false-case" is equal to "goal-statement false". -}
   false-case : length ys ≤ length (x :: xs)
   false-case = ≤-trans (length ys) (length xs) (length (x :: xs))
                  IH (≤-suc-lemma (length xs))

   {- The type of "true-case" is equal to "goal-statement true". -}
   true-case : length (x :: ys) ≤ length (x :: xs)
   true-case = ≤-suc (length ys) (length xs) IH

 {- Here is a version that uses Agda's built-in with-keyword (as shown by Eric in
    the lab of 28 Feb) instead of Bool-elim. (Under the hood, they amount to the
    same thing.) -}
length-of-filter' : {A : Type} (P : A → Bool) (xs : List A)
                  → length (filter P xs) ≤ length xs
length-of-filter' P []        = ≤-zero 0

length-of-filter' P (x :: xs) with P x
length-of-filter' P (x :: xs)    | true  = true-case
 where
  ys = filter P xs

  IH : length ys ≤ length xs
  IH = length-of-filter' P xs

  true-case : length (x :: ys) ≤ length (x :: xs)
  true-case = ≤-suc (length ys) (length xs) IH

length-of-filter' P (x :: xs)    | false = false-case
 where
  ys = filter P xs

  IH : length ys ≤ length xs
  IH = length-of-filter' P xs

  false-case : length ys ≤ length (x :: xs)
  false-case = ≤-trans (length ys) (length xs) (length (x :: xs))
                 IH (≤-suc-lemma (length xs))

length-of-filters : {A : Type} (P : A → Bool) (xs : List A)
                  → length (filter P xs) + length (filter (not ∘ P) xs)
                  ≡ length xs
length-of-filters P []        = refl _
length-of-filters P (x :: xs) = Bool-elim goal-statement false-case
                                                         true-case
                                                         (P x)
 where
  ys  = filter P xs
  ys' = filter (not ∘ P) xs

  IH : length ys + length ys' ≡ length xs
  IH = length-of-filters P xs

  {- Note that by definition
       filter P (x :: xs) = if P x then (x :: ys) else ys
     and so goal-statement is almost
         length (filter P         (x :: xs)) +
         length (filter (not ∘ P) (x :: xs))
       ≡ length (x :: xs)
     except that we replace "P x" by the Boolean "b". -}
  goal-statement : Bool → Type
  goal-statement b = length (if b     then (x :: ys ) else ys ) +
                     length (if not b then (x :: ys') else ys')
                   ≡ 1 + length xs

  {- The type of "false-case" is equal to "goal-statement false. -}
  false-case : length ys + length (x :: ys') ≡ length (x :: xs)
  false-case =
   length ys + length (x :: ys') ≡⟨ refl _                                    ⟩
   length ys + (1 + length ys')  ≡⟨ sym (+-assoc (length ys) 1 (length ys'))  ⟩
   (length ys + 1) + length ys'  ≡⟨ ap (_+ length ys') (+-comm (length ys) 1) ⟩
   (1 + length ys) + length ys'  ≡⟨ sym (+-assoc 1 (length ys) (length ys'))  ⟩
   1 + (length ys + length ys')  ≡⟨ ap (1 +_) IH                              ⟩
   1 + length xs                 ∎

   {- The type of "true-case" is equal to "goal-statement true". -}
  true-case : length (x :: ys) + length ys' ≡ length (x :: xs)
  true-case =
   length (x :: ys) + length ys' ≡⟨ refl _                             ⟩
   (1 + length ys) + length ys'  ≡⟨ +-assoc 1 (length ys) (length ys') ⟩
   1 + (length ys + length ys')  ≡⟨ ap (1 +_) IH                       ⟩
   1 + length xs                 ∎

{- Here is a version that uses Agda's built-in with-keyword (as shown by Eric in
   the lab of 28 Feb) instead of Bool-elim. (Under the hood, they amount to the
   same thing.) -}
length-of-filters' : {A : Type} (P : A → Bool) (xs : List A)
                   → length (filter P xs) + length (filter (not ∘ P) xs)
                   ≡ length xs
length-of-filters' P []        = refl _

length-of-filters' P (x :: xs) with P x
length-of-filters' P (x :: xs)    | true  = true-case
 where
  ys  = filter P xs
  ys' = filter (not ∘ P) xs

  IH : length ys + length ys' ≡ length xs
  IH = length-of-filters P xs

  true-case : length (x :: ys) + length ys' ≡ length (x :: xs)
  true-case =
   length (x :: ys) + length ys' ≡⟨ refl _                             ⟩
   (1 + length ys) + length ys'  ≡⟨ +-assoc 1 (length ys) (length ys') ⟩
   1 + (length ys + length ys')  ≡⟨ ap (1 +_) IH                       ⟩
   1 + length xs                 ∎

length-of-filters' P (x :: xs)    | false = false-case
 where
  ys  = filter P xs
  ys' = filter (not ∘ P) xs

  IH : length ys + length ys' ≡ length xs
  IH = length-of-filters P xs

  false-case : length ys + length (x :: ys') ≡ length (x :: xs)
  false-case =
   length ys + length (x :: ys') ≡⟨ refl _                                    ⟩
   length ys + (1 + length ys')  ≡⟨  sym (+-assoc (length ys) 1 (length ys'))   ⟩
   (length ys + 1) + length ys'  ≡⟨ ap (_+ length ys') (+-comm (length ys) 1) ⟩
   (1 + length ys) + length ys'  ≡⟨ sym (+-assoc 1 (length ys) (length ys'))  ⟩
   1 + (length ys + length ys')  ≡⟨ ap (1 +_) IH                              ⟩
   1 + length xs                 ∎
```

*Hint*: You can use associativity (`+-assoc`) and commutativity (`+-comm`) from
 the sample solutions to last week's exercises. (The necessary files are already
 imported for you.)
