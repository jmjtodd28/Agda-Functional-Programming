# Week 6 - Homework Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module lab6copy where

private
 open import prelude hiding (Bool-elim)
 open import natural-numbers-functions hiding (_≤_ ; is-even ; +-assoc )
 open import List-functions
 open import decidability
 open import isomorphisms
```
We will also want to use some things from the Lab of Week 4:

```agda
 open import solutions.lab4 hiding (_∘_;id;is-decidable;_≤_;≤-trans)

```

## Part I: More on length

Besides `map`, the function `reverse` is another example of a length-preserving
operation.

```agda

 length-of-++ : {A : Type} (xs ys : List A)
                → length (xs ++ ys) ≡ length xs + length ys
 length-of-++ []        ys = refl (length ys)
 length-of-++ (x :: xs) ys = ap suc IH
   where
     IH : length (xs ++ ys) ≡ length xs + length ys
     IH = length-of-++ xs ys

 length-of-reverse : {A : Type} (xs : List A)
                   → length (reverse xs) ≡ length xs
 length-of-reverse [] = refl 0
 length-of-reverse (x :: xs) = 
  length (reverse xs ++ [ x ])           ≡⟨ length-of-++ (reverse xs) [ x ] ⟩
  (length (reverse xs)) + length ([ x ]) ≡⟨ refl _ ⟩
  length (reverse xs) + 1                ≡⟨ +-step (length (reverse xs)) 0  ⟩
  suc (length (reverse xs) + 0)          ≡⟨ ap suc (+-base (length (reverse xs))) ⟩
  suc (length (reverse xs))              ≡⟨ ap suc (length-of-reverse xs) ⟩
  suc (length xs)                        ∎

 ```

**Prove** the above.

## Part II: More on isomorphisms

### Exercise 2a

```agda
 ℕ-[⋆]-iso : ℕ ≅ List 𝟙
 ℕ-[⋆]-iso = record { bijection = f ; bijectivity = f-is-bijection }
  where
   f : ℕ → List 𝟙
   f zero = []
   f (suc x) = ⋆ :: f x

   g : List 𝟙 → ℕ
   g [] = 0
   g (⋆ :: xs) = 1 + g xs

   gf : g ∘ f ∼ id
   gf zero = refl 0
   gf (suc x) = ap suc (gf x)

   fg : f ∘ g ∼ id
   fg [] = refl []
   fg (⋆ :: xs) = ap (⋆ ::_) (fg xs)

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
 ℕ→[⋆]-preserves-length zero = refl zero
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

```agda
 check-even : ℕ → Bool
 check-even zero          = true
 check-even (suc zero)    = false
 check-even (suc (suc n)) = check-even n
```

Now recall the discussion about decidable predicates that we had in the previous
weeks. When you proved that `check-even` and `is-even` are logically equivalent
in the lab, you have in fact implicitly proved that `is-even` is a decidable
predicate! In this exercise, we will make this implicit proof _explicit_.

**Complete** the remaining holes in the following proof outline; starting with
proving a lemma stating that a Boolean is either `true` or `false`.

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

 even⇒check-even : (n : ℕ) → is-even n → check-even n ≡ true
 even⇒check-even zero _ = refl true
 even⇒check-even (suc zero) (suc zero , ())
 even⇒check-even (suc zero) (suc (suc _) , ())
 even⇒check-even (suc (suc n)) p = even⇒check-even n (evenness-lemma₁ n p)

 check-even⇒even : (n : ℕ) → check-even n ≡ true → is-even n
 check-even⇒even zero (refl true) = zero , refl zero
 check-even⇒even (suc zero) ()
 check-even⇒even (suc (suc n)) p = evenness-lemma₂ n (check-even⇒even n p)

 principle-of-bivalence : (b : Bool) → (b ≡ true) ∔ (b ≡ false)
 principle-of-bivalence true = inl (refl true)
 principle-of-bivalence false = inr (refl false)

 is-even-is-decidable : (n : ℕ) → is-decidable (is-even n)
 is-even-is-decidable n =
  ∔-nondep-elim goal₁ goal₂ (principle-of-bivalence (check-even n))
   where
    goal₁ : check-even n ≡ true → is-decidable (is-even n)
    goal₁ p = inl (check-even⇒even n p )

    goal₂ : check-even n ≡ false → is-decidable (is-even n)
    goal₂ p = inr subgoal
     where
      subgoal : ¬ is-even n
      subgoal q = {!!}
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


 length-of-filter : {A : Type} (P : A → Bool) (xs : List A)
                  → length (filter P xs) ≤ length xs
 length-of-filter P [] = ≤-zero zero
 length-of-filter P (x :: xs) with P x
 ... | true = ≤-suc (length (filter P xs)) (length xs) (length-of-filter P xs)
 ... | false = ≤-trans
               (length (filter P xs)) (length xs) (suc (length xs))
               (length-of-filter P xs) (≤-suc-lemma (length xs)) 
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
 lemma : (x y : ℕ) → x + suc y ≡ suc x + y
 lemma zero y = refl _
 lemma (suc x) y = ap suc (+-step x y)

 length-of-filters : {A : Type} (P : A → Bool) (xs : List A)
                   → length (filter P xs) + length (filter (not ∘ P) xs)
                   ≡ length xs
 length-of-filters P [] = refl 0
 length-of-filters P (x :: xs) with P x
 ... | true = ap suc (length-of-filters P xs)
 ... | false = 
              length (filter P xs) + suc (length (filter (λ x₁ → not (P x₁)) xs))
                ≡⟨ lemma (length (filter P xs)) (length (filter (λ x₁ → not (P x₁)) xs)) ⟩
              suc (length (filter P xs) + length (filter (λ x₁ → not (P x₁)) xs))
                ≡⟨ ap suc (length-of-filters P xs) ⟩
              suc (length xs) ∎

```

*Hint*: You can use associativity (`+-assoc`) and commutativity (`+-comm`) from
 the sample solutions to last week's exercises. (The necessary files are already
 imported for you.)
