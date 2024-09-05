# Week 4 - Lab Sheet

```agda
module lab4copy where
open import prelude hiding (id;_∘_)
open import List-functions hiding (map)

private
```

## Part I: Reverse is an involution

We wish to prove that the `reverse` function on lists is an involution;
that is to say that reversing a list twice is the same as doing nothing.

### Exercise 1.1

First, we will prove the following lemma.

```agda
 reverse-lemma : {X : Type} (x : X) (xs : List X)
               → x :: reverse xs ≡ reverse (xs ++ [ x ])
 reverse-lemma y [] = refl _
 reverse-lemma y (x :: xs) = ap (_++ [ x ]) (reverse-lemma y xs)
```

**Prove** the lemma about `reverse`.

### Exercise 1.2

The following proof skeleton has been provided for you, using [notation for
equational reasoning][0].

```agda
 reverse-is-involution : {X : Type} → (xs : List X) → xs ≡ reverse (reverse xs)
 reverse-is-involution [] = refl []
 reverse-is-involution (x :: xs)
  = x :: xs                       ≡⟨ ap (x ::_) (reverse-is-involution xs) ⟩
    x :: reverse (reverse xs)     ≡⟨ reverse-lemma x (reverse xs) ⟩
    reverse (reverse xs ++ [ x ]) ≡⟨ refl _ ⟩
    reverse (reverse (x :: xs))   ∎
```

**Fill** the holes of our proof that `reverse` is an involution.

## Part II: Associativity of addition of natural numbers

We wish to prove the associativity of `_+_` on the natural numbers.

```agda
 +-assoc : (x y z : ℕ) → x + (y + z) ≡ (x + y) + z
 +-assoc zero y z = refl (y + z)
 +-assoc (suc x) y z = ap suc (+-assoc x y z)
```

**Complete** the proof that `_+_` is associative.

## Part III: Laws for `map`

Recall that we defined `map` as follows:
```
 map : {A B : Type} → (A → B) → List A → List B
 map f []        = []
 map f (x :: xs) = f x :: map f xs
```

In Haskell, `map` is supposed to satisfy, for every list `xs`, two laws:

  1. `map id xs = xs` (where `id` the identity function);
  1. `map (g . f) xs = map g (map f xs)` (where `.` is function composition).

But checking these laws is left to a pen-and-paper check by the programmer.

In Agda, we can both *state* and *prove* these laws.

We first define function composition and the identity function.

```agda
 id : {A : Type} → A → A
 id = λ x → x

 _∘_ : {A B C : Type} → (g : B → C) → (f : A → B)→ A → C
 g ∘ f = λ x → g (f x)
```

Tip: Use `\comp` to type `∘`.

### Exercise 3.1

The first `map` law can now be written in Agda as
```agda
 map-law1 : {A : Type} (xs : List A) → map id xs ≡ xs
 map-law1 [] = refl []
 map-law1 (x :: xs) = ap (x ::_) (map-law1 xs)
```

**Define** this function. (Hint: An induction hypothesis comes in helpful).

### Exercise 3.2

A partial statement of the second `map` law is the following:
```agda
 map-law2 : {A B C : Type} (g : B → C) (f : A → B) (xs : List A)
          → map (g ∘ f) xs ≡ map g (map f xs)
 map-law2 g f [] = refl []
 map-law2 g f (x :: xs) = ap (g (f x) ::_) (map-law2 g f xs)
```

**Complete** the holes in `map-law2 : ...`, i.e. write down the types of `g` and
`f`, and translate the second `map` law `map (g ∘ f) xs = map g (map f xs)` to
Agda.


### Exercise 3.3

Now **complete** the proof of `map-law2`.


## Part IV: Decidability and decidable equality

Recall the definition of a *decidable type* from the lecture notes:


```agda
 is-decidable : Type → Type
 is-decidable A = A ∔ ¬ A
```

To assert `is-decidable A` for some type `A` is to say that type `A` satisfies
the law of excluded middle: we can either construct an inhabitant of `A` or
prove that the existence of an inhabitant for `A` is impossible.

We will often be interested in the _decidability of equality types_. A
type `A` is said to have _decidable equality_ iff for any two `x y :
A`, the identity type `x ≡ y` is decidable. We can write this notion
down in Agda as follows:

```agda
 has-decidable-equality : Type → Type
 has-decidable-equality A = (x y : A) → is-decidable (x ≡ y)
```

### Exercise 4.1 

To familiarise yourself with the notion of decidable equality, **prove** that
the `Bool` type has decidable equality:

```agda
 bool-has-decidable-equality : has-decidable-equality Bool
 bool-has-decidable-equality true true = inl (refl true)
 bool-has-decidable-equality true false = inr λ z → lemma z
   where
     lemma : true ≡ false → 𝟘
     lemma ()
 bool-has-decidable-equality false true = inr λ z → lemma z
   where
     lemma : false ≡ true → 𝟘
     lemma ()
 bool-has-decidable-equality false false = inl (refl false)

```

### Exercise 4.2

In the lecture, we stated that a type was decidable if and only if one could find a `b : Bool` such that `A` holds if and only if the boolean `b` is `true`.  A proof appears in the lecture notes, but it is a nice exercise to do it for yourself:

```agda
 decidability-with-booleans : (A : Type) → is-decidable A ⇔ Σ b ꞉ Bool , (A ⇔ b ≡ true)
 decidability-with-booleans A = f , g
   where
     f : is-decidable A → Sigma Bool (λ b → A ⇔ b ≡ true)
     f (inl x) = true , α , β
       where
         α : A → true ≡ true
         α z = refl true

         β : true ≡ true → A
         β z = x

     f (inr x) = false , α , β
       where
         α : A → false ≡ true
         α z = 𝟘-elim (x z)

         β : false ≡ true → A
         β ()

     g : Sigma Bool (λ b → A ⇔ b ≡ true) → is-decidable A
     g (true , f , g) = inl (g (refl (true)))
     g (false , f , g) = inr λ z → lemma (f z)
       where
         lemma : false ≡ true → 𝟘
         lemma ()
```

### Exercise 4.3 (Harder)

Recall the following definitions of decidable predicates and "exhaustively searchable" types from
the [lecture notes](../decidability.lagda.md)

```agda
 is-decidable-predicate : {X : Type} → (X → Type) → Type
 is-decidable-predicate {X} A = (x : X) → is-decidable (A x)

 is-exhaustively-searchable : Type → Type₁
 is-exhaustively-searchable X = (A : X → Type)
                              → is-decidable-predicate A
                              → is-decidable (Σ x ꞉ X , A x)
```                              

Now, for each `n`, we can construct a type with exactly `n` elements as follows:

```agda
 data Fin : ℕ → Type where
  zero : {n : ℕ} → Fin (suc n)
  succ : {n : ℕ} → Fin n → Fin (suc n)
```
(You can read more about this type [here](../Fin.lagda.md))

Show that `Fin n` is exhaustively searchable for every `n`.

```agda
 Fin-is-exhaustively-searchable : (n : ℕ) → is-exhaustively-searchable (Fin n)
 Fin-is-exhaustively-searchable zero A x = {! !}
 Fin-is-exhaustively-searchable (suc n) A x = {!!}
```

## Part V: Associativity and Commutativity of ∔ and ×

We have already seen that the Boolean operations `_||_` and `_&&_` are
associative and commutative.

The type formers that represent these logical connectives are also associative
and commutative.

### Exercise 5.1

**Prove** that `_∔_` is associative.

```agda
 ∔-assoc : {A B C : Type} → A ∔ (B ∔ C) → (A ∔ B) ∔ C
 ∔-assoc (inl x) = inl (inl x)
 ∔-assoc (inr (inl x)) = inl (inr x)
 ∔-assoc (inr (inr x)) = inr x
```

### Exercise 5.2

**Prove** that `_×_` is associative.

```agda
 ×-assoc : {A B C : Type} → A × (B × C) → (A × B) × C
 ×-assoc (a , b , c) = (a , b) , c
```

### Exercise 5.3

**Prove** that `_∔_` is commutative.

```agda
 ∔-comm : {A B : Type} → A ∔ B → B ∔ A
 ∔-comm (inl x) = inr x
 ∔-comm (inr x) = inl x
```
### Exercise 5.4

**Prove** that `_×_` is commutative.

```agda
 ×-comm : {A B : Type} → A × B → B × A
 ×-comm (x , y) = y , x
```

## Part VI: Order on the natural numbers

In this part we will study two ways of expressing that a natural number is less
than or equal to another natural number.

The first definition is an inductive one.

```agda
 data _≤_ : ℕ → ℕ → Type where
  ≤-zero : (  y : ℕ) → 0 ≤ y
  ≤-suc  : (x y : ℕ) → x ≤ y → suc x ≤ suc y
```

It says:
1. that zero is less than or equal to any natural number;
1. if `x` is less than or equal to `y`, then `suc x` is less than or equal to `suc y`.

The second definition uses a `Σ`-type.

```agda
 _≤'_ : ℕ → ℕ → Type
 x ≤' y = Σ k ꞉ ℕ , x + k ≡ y
```

It says that `x` is less than or equal to `y` if we have some `k : ℕ`
such that `x + k ≡ y`.

We will prove that the two definitions are logically equivalent.

### Exercise 6.1

In order to prove that the first definition implies the second, we first
prove two little lemmas about `_≤'_`.

Note that they amount to the constructors of `_≤_`.

```agda
 ≤'-zero : (y : ℕ) → 0 ≤' y
 ≤'-zero y = y , refl y

 ≤'-suc : (x y : ℕ) → x ≤' y → suc x ≤' suc y
 ≤'-suc x y (z , e) = z , ap suc e
```

**Prove** the two little lemmas about `_≤'_`.

### Exercise 6.2

We now prove that the first definition implies the second.

```agda
 ≤-prime : (x y : ℕ) → x ≤ y → x ≤' y
 ≤-prime .0 y (≤-zero .y) =  ≤'-zero y
 ≤-prime .(suc x) .(suc y) (≤-suc x y e) = ≤'-suc x y (≤-prime x y e)
```

**Prove** that `x ≤ y` implies `x ≤' y` using the little lemmas from 3.1.

### Exercise 6.3

The other direction is slightly trickier.

```agda
 ≤-unprime : (x y : ℕ) → x ≤' y → x ≤ y
 ≤-unprime zero y e = ≤-zero y
 ≤-unprime (suc x) .(suc x + z) (z , refl .(suc x + z)) = ≤-suc x (x + z) (≤-unprime x (x + z) (z , refl _))
```

**Prove** that `x ≤' y` implies `x ≤ y`.

*Hint:* The base case only requires pattern matching on `x`, whereas
the inductive case requires further pattern matching.

### Exercise 6.4

The order on the natural numbers is transitive, meaning that if
`x ≤ y` and `y ≤ z` then also `x ≤ z`. We can prove this for
both our definitions of the order.

```agda
 ≤-trans : (x y z : ℕ) → x ≤ y → y ≤ z → x ≤ z
 ≤-trans zero y z p q = ≤-zero z
 ≤-trans (suc x) .(suc y) .(suc z) (≤-suc .x y p) (≤-suc .y z q) = ≤-suc x z (≤-trans x y z p q)

 ≤'-trans : (x y z : ℕ) → x ≤' y → y ≤' z → x ≤' z
 ≤'-trans x .(x + a) .((x + a) + b) (a , refl .(x + a)) (b , refl .((x + a) + b)) = a + b , +-assoc x a b
```

**Complete** the proofs that `_≤_` and `_≤'_` are transitive.



[0]: ../identity-type.lagda.md#notation-for-equality-reasoning

