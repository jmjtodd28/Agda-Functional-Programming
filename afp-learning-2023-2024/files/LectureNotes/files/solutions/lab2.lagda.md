# Week 2 - Lab Sheet

Do as much as you can in the lab, and complete the remaining exercises in your own time. Feel free to ask questions on Teams in the channel `lab`. But don't give spoilers there.

```agda
module solutions.lab2 where

open import prelude hiding (if_then_else_;_||_)

module _ where -- was private
```

## Part I: Booleans

### Section 1: Operations on Booleans

#### Exercise 1.1

We have already defined `if-then-else` like so:

```agda
 if_then_else_ : {A : Type} → Bool → A → A → A
 if true  then x else y = x
 if false then x else y = y
```

But this requires our two branches to be of the same type A. Instead, we could
define `if-then-else` to have branches of different types, using the `_∔_`
type constructor.

```agda
 if'_then_else_ : {A B : Type} → Bool → A → B → A ∔ B
 if' true  then x else y = inl x
 if' false then x else y = inr y
```

**Define** this function.

#### Exercise 1.2

We can define the `_||_` function in (at least) two different ways, depending on
how much pattern-matching we wish to perform:

```agda
 _||_ : Bool → Bool → Bool
 true  || y = true
 false || y = y

 _||'_ : Bool → Bool → Bool
 true  ||' true  = true
 true  ||' false = true
 false ||' true  = true
 false ||' false = false
```

**Complete** the two holes for `_||_` and the four holes for `_||'_`.

The `_||_` operator is *associative*, meaning `a || (b || c) ≡ (a || b) || c`.

We can prove this for both of our definitions:

```agda
 ||-assoc : (a b c : Bool)  → a ||  (b ||  c) ≡ (a ||  b) || c
 ||-assoc true  b c = refl true
 ||-assoc false b c = refl (b || c)

 ||'-assoc : (a b c : Bool) → a ||' (b ||' c) ≡ (a ||' b) ||' c
 ||'-assoc true  true  true  = refl true
 ||'-assoc true  true  false = refl true
 ||'-assoc true  false true  = refl true
 ||'-assoc true  false false = refl true
 ||'-assoc false true  true  = refl true
 ||'-assoc false true  false = refl true
 ||'-assoc false false true  = refl true
 ||'-assoc false false false = refl false
```

**Complete** both of these proofs.

**Hint**. Try to use `refl` to prove equalities, which can be used when Agda calculates that two things are equal (see the [identity type](../identity-type.lagda.md) handout for more details).

**Hint**. Because `_||_` was defined by pattern matching on the first argument, it
may be helpful to use the same strategy.

Which of these did you prefer proving, and why?

#### Exercise 1.3

**Complete** the proof that Boolean disjunction is commutative:

```agda
 ||-is-commutative : (a b : Bool) → a || b ≡ b || a
 ||-is-commutative true  true  = refl true
 ||-is-commutative true  false = refl true
 ||-is-commutative false true  = refl true
 ||-is-commutative false false = refl false
```

#### Exercise 1.4

**Complete** the proof that `false` is the left unit element of `_||_`:

```agda
 false-left-unit-for-|| : (b : Bool) → false || b ≡ b
 false-left-unit-for-|| b = refl b
```

**Complete** the proof that `false` is the right unit element of `_||_`:

```agda
 false-right-unit-for-|| : (b : Bool) → b || false ≡ b
 false-right-unit-for-|| true  = refl true
 false-right-unit-for-|| false = refl false
```

#### Exercise 1.5

Now prove the analogous properties for `_&&_`.

**Complete** the proof that Boolean conjunction is associative:

```agda
 &&-is-associative : (a b c : Bool) → a && (b && c) ≡ (a && b) && c
 &&-is-associative true  b c = refl (b && c)
 &&-is-associative false b c = refl false
```

**Complete** the proof that Boolean conjunction is commutative:

```agda
 &&-is-commutative : (a b : Bool) → a && b ≡ b && a
 &&-is-commutative true  true  = refl true
 &&-is-commutative true  false = refl false
 &&-is-commutative false true  = refl false
 &&-is-commutative false false = refl false
```

**Complete** the proof that that `true` is the left unit element of `_&&_`:

```agda
 true-left-unit-for-&& : (b : Bool) → true && b ≡ b
 true-left-unit-for-&& b = refl b
```

**Complete** the proof that that `true` is the right unit element of `_&&_`:

```agda
 true-right-unit-for-&& : (b : Bool) → b && true ≡ b
 true-right-unit-for-&& true  = refl true
 true-right-unit-for-&& false = refl false
```

#### Exercise 1.6

An important algebraic property between two operators is *distributivity*. For
example, multiplication distributes over addition since `x * (y + z) = (x * y) +
(x * z)` for every `x, y, z ∈ ℕ`. The same is the case for the Boolean
conjunction and disjunction operators we have defined.

**Complete** the proof that Boolean conjunction distributes over Boolean
disjunction:

```agda
 &&-distributes-over-|| : (a b c : Bool) → a && (b || c) ≡ (a && b) || (a && c)
 &&-distributes-over-|| true  b c = refl (b || c)
 &&-distributes-over-|| false b c = refl false
```

```agda
 ||-distributes-over-&& : (a b c : Bool) → a || (b && c) ≡ (a || b) && (a || c)
 ||-distributes-over-&& true  b c = refl true
 ||-distributes-over-&& false b c = refl (b && c)
```

### Section 2: Identity type and `Bool`

With these exercises, you will practise with the identity type and `Bool`.

#### Exercise 2.1

Recall how we defined `_≣_` for [natural
numbers](../introduction.lagda.md#the-empty-type-and-the-unit-type). We could do
the same for the Booleans.

```agda
 _≣_ : Bool → Bool → Type
 true  ≣ true  = 𝟙
 true  ≣ false = 𝟘
 false ≣ true  = 𝟘
 false ≣ false = 𝟙
```

**Define** this function.

Tip: you can type `≣` as `\===`.

#### Exercise 2.2

We can also define a Boolean-valued equality function.

```agda
 _==_ : Bool → Bool → Bool
 true  == true  = true
 true  == false = false
 false == true  = false
 false == false = true
```

**Define** this function.

#### Exercise 2.3

Now we write a conversion function from `x ≡ y` to `x ≣ y`, just like the
function `back` in
[introduction](../introduction.lagda.md#the-identity-type-former-__).

```agda
 ≡-to-≣ : (x y : Bool) → x ≡ y → x ≣ y
 ≡-to-≣ true  true e  = ⋆
 ≡-to-≣ false false e = ⋆
```

**Complete** this function.

#### Exercise 2.4

The following helper function makes some functions nicer to read.

```agda
 is-true : Bool → Type
 is-true b = b ≡ true
```

Now we can consider another conversion function.

```agda
 ≣-to-== : (x y : Bool) → x ≣ y → is-true (x == y)
 ≣-to-== true  true  e = refl true
 ≣-to-== false false e = refl true
```

**Define** this function.

#### Exercise 2.5

And similarly, we have

```agda
 ==-to-≡ : (x y : Bool) → is-true (x == y) → x ≡ y
 ==-to-≡ true  true  e = refl true
 ==-to-≡ false false e = refl false
```

**Define** this function.

#### Exercise 2.6

Finally, we can use the above functions to define the three remaining
implications

```agda
 ≡-to-== : (x y : Bool) → x ≡ y → is-true (x == y)
 ≡-to-== x y e = ≣-to-== x y (≡-to-≣ x y e)

 ≣-to-≡ : (x y : Bool) → x ≣ y → x ≡ y
 ≣-to-≡ x y e = ==-to-≡ x y (≣-to-== x y e)

 ==-to-≣ : (x y : Bool) → is-true (x == y) → x ≣ y
 ==-to-≣ x y e = ≡-to-≣ x y (==-to-≡ x y e)
```

**Complete** these functions.


## Part II: Homework

First, take a look at how we define

 * the type of [natural numbers](../natural-numbers-type.lagda.md) and
 * the [identity type](../identity-type.lagda.md).

### Section 1: Some functions on natural numbers

#### Exercise 1.1

**Complete** the proof of the fact that `(suc x) + y ≡ suc (x + y)`

```agda
 +-suc-on-left : (x y : ℕ) → (suc x) + y ≡ suc (x + y)
 +-suc-on-left x y = refl (suc (x + y))
```

#### Exercise 1.2

We can define the `max` operation on natural numbers as follows:

```agda
 max : ℕ → ℕ → ℕ
 max zero    n       = n
 max (suc m) zero    = suc m
 max (suc m) (suc n) = suc (max m n)
```

**Define** the function `min` analogously:

```agda
 min : ℕ → ℕ → ℕ
 min 0       n       = 0
 min (suc m) 0       = 0
 min (suc m) (suc n) = suc (min m n)
```

### Section 2: Natural numbers and proofs using induction

The function `+-0-on-right` expresses the fact that `0` is a right unit of the
operation `_+_`. Notice how we use an inductive hypothesis (the recursive call)
in the proof. (Spelling this out, `IH` tells us that `x + 0 ≡ x`, so that `ap
suc IH` witnesses that `suc (x + 0) ≡ suc x`.)

```agda
 +-0-on-right : (x : ℕ) → x + 0 ≡ x
 +-0-on-right zero    = refl zero
 +-0-on-right (suc x) = ap suc IH
  where
   IH : x + 0 ≡ x -- IH is short for induction hypothesis
   IH = +-0-on-right x
```

Using similar induction hypotheses, try to complete the following exercises.


#### Exercise 2.1

**Complete** the proof:

```agda
 +-suc-on-right : (x y : ℕ) → x + suc y ≡ suc (x + y)
 +-suc-on-right zero    y = refl (suc y)
 +-suc-on-right (suc x) y = ap suc (+-suc-on-right x y)
```

#### Exercise 2.2

In algebra, an operator `_*_` is called idempotent iff `x * x = x` for every
`x`. `max` is an example of an idempotent operator:

**Complete** the hole to prove that `max` is idempotent:

```agda
 max-idempotent : (x : ℕ) → max x x ≡ x
 max-idempotent zero    = refl zero
 max-idempotent (suc x) = ap suc (max-idempotent x)
```

#### Exercise 2.3

**Complete** the hole by constructing a proof of the fact that `max` is a
commutative operator:

```agda
 max-commutative : (x y : ℕ) → max x y ≡ max y x
 max-commutative zero    zero    = refl zero
 max-commutative zero    (suc y) = refl (suc y)
 max-commutative (suc x) zero    = refl (suc x)
 max-commutative (suc x) (suc y) = ap suc (max-commutative x y)
```

#### Exercise 2.4

Now recall that we defined `min` in Exercise 1.2. Similarly, we can show that
`min` is idempotent and commutative too.

**Complete** the proof that `min` is idempotent:

```agda
 min-idempotent : (x : ℕ) → min x x ≡ x
 min-idempotent zero    = refl zero
 min-idempotent (suc x) = ap suc (min-idempotent x)
```

#### Exercise 2.5

**Complete** the proof that `min` is commutative:

```agda
 min-commutative : (x y : ℕ) → min x y ≡ min y x
 min-commutative zero    zero    = refl zero
 min-commutative zero    (suc y) = refl zero
 min-commutative (suc x) zero    = refl zero
 min-commutative (suc x) (suc y) = ap suc (min-commutative x y)
```
