# Week 8 - Lab Sheet

```agda
{-# OPTIONS --safe --without-K --auto-inline #-}

module lab8 where

open import prelude
open import decidability
open import Fin
open import List-functions
open import isomorphisms
open import sorting
open import strict-total-order
```

In this lab sheet you will practice with **strict total orders** and **positions**.

## Exercise 1 - The Lexicographical Order on `ℕ × ℕ`

The *lexicographical order* on `ℕ²` is defined as: `(n , m) < (n' , m')`
precisely when (`n < n'`) or (`n = n'` and `m < m'`).

So, for example, `(3 , 19) < (5, 2)` and `(7 , 3) < (7 , 4)`, but `¬ (11 , 4) <
(11 , 1)` and `¬ (5 , 1) < (4 , 3)`.

We are going to prove that the lexicographical order is a strict total order on
`ℕ²`.

### Exercise 1.1

**Translate** the definition of the lexicographical order to Agda.

```agda
module _ where

 open StrictTotalOrder ℕ-StrictTotalOrder

 ℕ² : Type
 ℕ² = ℕ × ℕ

 _<ₗ_ : ℕ² → ℕ² → Type
 (n , m) <ₗ (n' , m') = (n <ₙ n') ∔ ((n ≡ n') × (m <ₙ m'))
```

### Exercise 1.2

**Prove** that the lexicographical order is irreflexive.

```agda
 <ₗ-is-irreflexive : (p : ℕ²) → ¬ (p <ₗ p)
 <ₗ-is-irreflexive (a , b) (inl x) = irreflexive a x
 <ₗ-is-irreflexive (a , b) (inr (p , q)) = irreflexive b q
```

### Exercise 1.3

**Prove** that the lexicographical order is transitive.

```agda
 <ₗ-is-transitive : {p q r : ℕ²} → p <ₗ q → q <ₗ r → p <ₗ r
 <ₗ-is-transitive {n , m} {n' , m'} {n'' , m''} (inl n<n') (inl n'<n'') = inl (transitive n<n' n'<n'')
 <ₗ-is-transitive {n , m} {n' , m'} {.n' , m''} (inl n<n') (inr (refl .n' , b)) = inl n<n'
 <ₗ-is-transitive {n , m} {.n , m'} {n'' , m''} (inr (refl .n , m<m')) (inl y) = inl y
 <ₗ-is-transitive {n , m} {.n , m'} {.n , m''} (inr (refl n , x)) (inr (refl .n , m'<m''))
                                               = inr (refl n , transitive x m'<m'')


-- <ₗ-is-transitive {p} {q} {r} (inl x) (inl y) = inl (transitive x y)
-- <ₗ-is-transitive {n , m} {.n , m'} {n'' , m''} (inr (a , b)) (inl y) = {!!}
-- <ₗ-is-transitive {p} {q} {r} (inl x) (inr y) = {!!}
-- <ₗ-is-transitive {p} {q} {r} (inr x) (inr y) = inr ((trans (fst x) (fst y)) , (transitive (snd x) (snd y)))

 <ₗ-is-transitive' : {p q r : ℕ²} → p <ₗ q → q <ₗ r → p <ₗ r
 <ₗ-is-transitive' {n , m} {n' , m'} {n'' , m''} (inl n<n') (inl n'<n'') = inl (<ₙ-trans n<n' n'<n'')
 <ₗ-is-transitive' {n , m} {n' , m'} {n'' , m''} (inl n<n') (inr (refl n' , _)) = inl n<n'
 <ₗ-is-transitive' {n , m} {.n , m'} {n'' , m''} (inr (refl n , m<m')) (inl n<n'') = inl n<n''
 <ₗ-is-transitive' {n , m} {.n , m'} {n'' , m''} (inr (refl n , m<m')) (inr (refl n , m'<m'')) = goal
                 where
                 goal : (n <ₙ n) ∔ ((n ≡ n) × (m <ₙ m''))
                 goal = inr (refl n , <ₙ-trans m<m' m'<m'')


```

### Exercise 1.4

**Prove** that the lexicographical is connected.

```agda
 <ₗ-is-connected : {p q : ℕ²} → ¬ (p ≡ q) → (p <ₗ q) ∔ (q <ₗ p)
 <ₗ-is-connected {n , m} {n' , m'} x with ℕ-has-decidable-equality n n' , ℕ-has-decidable-equality m m'
 ... | inl (refl .n) , inl (refl .m) = 𝟘-elim (x (refl (n , m) ))
 ... | inl (refl .n) , inr b = {!!}
 ... | inr a , b = {!!}

 
```

### Exercise 1.5

We will also need to prove that `ℕ × ℕ` has decidable equality.  Let's show
this more generally:

**Prove** that if `X` and `Y` have decidable equality, then so does their
cartesian product `X × Y`.

```agda
×-has-decidable-equality : {X Y : Type}
                         → has-decidable-equality X
                         → has-decidable-equality Y
                         → has-decidable-equality (X × Y)
×-has-decidable-equality p q (x , y) (x' , y') = lemma (p x x' , q y y')
  where
    lemma : (x ≡ x') ∔ ¬ (x ≡ x')
          × (y ≡ y') ∔ ¬ (y ≡ y')
          → is-decidable ((x , y) ≡ (x' , y'))
    lemma (inl (refl .x) , inl (refl .y)) = inl (refl(x' , y'))
    lemma (inl (refl .x) , inr y) = inr (λ z → y (ap snd z))
    lemma (inr x , inl (refl .y)) = inr (λ z → x (ap fst z))
    lemma (inr x , inr y) = inr (λ z → x (ap fst z))
```

**Conclude** that `ℕ × ℕ` has decidable equality.

```agda
ℕ²-has-decidable-equality : has-decidable-equality ℕ²
ℕ²-has-decidable-equality = ×-has-decidable-equality ℕ-has-decidable-equality  ℕ-has-decidable-equality
```

### Exercise 1.6

**Conclude** that the lexicographical order is a strict total order on `ℕ²`.

```agda
strict-total-order-on-ℕ² : StrictTotalOrder ℕ²
strict-total-order-on-ℕ² = record
                            { _<_ = _<ₗ_
                            ; irreflexive = <ₗ-is-irreflexive
                            ; transitive = <ₗ-is-transitive
                            ; connected = <ₗ-is-connected
                            ; ≡-is-decidable = ℕ²-has-decidable-equality
                            }
```

## Exercise 2 - Non-Strict Total Orders

In the lectures, a type of strict total order was introduced. Similarly, we can
also introduce a type of *non-strict total orders*.

For example, the type of natural numbers with `≤` is an example of a non-strict
total order.

```agda
record NonStrictTotalOrder (X : Type) : Type₁ where
 field
  _≤_ : X → X → Type
  ≡-is-decidable : has-decidable-equality X
  reflexive : (x : X) → x ≤ x
  transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
  antisymmetric : {x y : X} → x ≤ y → y ≤ x → x ≡ y
  strongly-connected : (x y : X) → (x ≤ y) ∔ (y ≤ x)
```

Now let's assume that we are given a *strict* total order. We make this
assumption using a module, which means it will be available to you in the code
below.

```agda
module _
        {X : Type}
        (sto : StrictTotalOrder X)
       where

 open StrictTotalOrder sto
```

Recall that in [strict-total-order](../strict-total-order.lagda.md#sorted-lists), we defined the order `≤` from the strict total order `<`.

```agdacode
 _≤_ : X → X → Type
 x ≤ y = (y ≡ x) ∔ (x < y)
```

Notice how `≤` was (implicitly) used in the definition of `Sorted` given in that file.

### Exercise 2.1

**Prove** the following facts about `≤`.

```agda
 <-to-≤ : {x y : X} → x < y → x ≤ y
 <-to-≤ x = inr x

 ≤-is-reflexive : (x : X) → x ≤ x
 ≤-is-reflexive x = inl (refl x)
```

### Exercise 2.2

Using transitivity of `<`, **prove** a lemma and that `≤` is transitive.

```agda
 <-≤-trans : {x y z : X} → x < y → y ≤ z → x ≤ z
 <-≤-trans p (inl (refl _)) = <-to-≤ p
 <-≤-trans p (inr q) = <-to-≤ (transitive p q)

 ≤-is-transitive : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
 ≤-is-transitive (inl (refl _)) q = q
 ≤-is-transitive (inr x) (inl (refl _)) = <-to-≤ x
 ≤-is-transitive (inr x) (inr q) = <-to-≤ (transitive x q)

 ≤-is-transitive' : {x y z : X} → x ≤ y → y ≤ z → x ≤ z
 ≤-is-transitive' (inl (refl _)) y = y
 ≤-is-transitive' (inr x) y = <-≤-trans x y

```

### Exercise 2.3

**Prove** antisymmetry of `≤`.

```agda
 ≤-is-antisymmetric : {x y : X} → x ≤ y → y ≤ x → x ≡ y
 ≤-is-antisymmetric x (inl y) = y
 ≤-is-antisymmetric (inl x) (inr y) = sym x
 ≤-is-antisymmetric (inr x) (inr y) = 𝟘-elim (antisymmetric _ _ x y)
```

### Exercise 2.4

**Show** that `≤` is strongly connected.

```agda
 ≤-is-strongly-connected : (x y : X) → (x ≤ y) ∔ (y ≤ x)
 ≤-is-strongly-connected x y with trichotomy x y
 ... | inl x<y       = inl (<-to-≤ x<y)
 ... | inr (inl x≡y) = inr (inl x≡y)
 ... | inr (inr x>y) = inr (inr x>y)

 ≤-is-strongly-connected' : (x y : X) → (x ≤ y) ∔ (y ≤ x)
 ≤-is-strongly-connected' x y = lemma (≡-is-decidable x y) 
   where
     lemma : (x ≡ y) ∔ ¬ (x ≡ y) → (x ≤ y) ∔ (y ≤ x)
     lemma (inl x) = inr (inl x)
     lemma (inr x) with connected x
     ... | inl p = inl (inr p)
     ... | inr q = inr (inr q)

 ≤-is-strongly-connected'' : (x y : X) → (x ≤ y) ∔ (y ≤ x)
 ≤-is-strongly-connected'' x y with ≡-is-decidable x y
 ... | inl e = inr (inl e )
 ... | inr x with connected x 
 ... | inl p = inl (inr p)
 ... | inr q = inr (inr q)
```

### Exercise 2.5

Finally, **complete** the definition of the non-strict total order on `X`.

```agda
 non-strict-total-order-from-strict-total-order : NonStrictTotalOrder X
 non-strict-total-order-from-strict-total-order =
     record
      { _≤_ = _≤_
      ; ≡-is-decidable = ≡-is-decidable 
      ; reflexive = ≤-is-reflexive
      ; transitive = ≤-is-transitive
      ; antisymmetric = ≤-is-antisymmetric
      ; strongly-connected = ≤-is-strongly-connected
      }
```

## Exercise 3 - More on Positions

Recall from the lectures that we defined a type of *positions* (or indices) for
a given list as follows.

```agdacode
Pos : {X : Type} → List X → Type
Pos        [] = 𝟘
Pos (_ :: xs) = 𝟙 ∔ Pos xs
```

We will consider an inductively defined version of here and prove it to be
isomorphic to `Pos`.

The inductive definition is as follows.

```agda
data Pos' {X : Type} : List X → Type where
  here : {x : X} {xs : List X}
       → Pos' (x :: xs)
  there : {x : X} {xs : List X}
        → (p : Pos' xs) → Pos' (x :: xs)
```

### Exercise 3.1

**Define** a function from `Pos xs` to `Pos' xs`.

```agda
Pos-to-Pos' : {X : Type} (xs : List X) → Pos xs → Pos' xs
Pos-to-Pos' [] =  𝟘-elim
Pos-to-Pos' (x :: xs) (inl ⋆) = here
Pos-to-Pos' (x :: xs) (inr p) = there (Pos-to-Pos' xs p)
```

### Exercise 3.2

**Define** a function the other way, i.e. from `Pos' xs` to `Pos xs`.

```agda
Pos'-to-Pos : {X : Type} (xs : List X) → Pos' xs → Pos xs
Pos'-to-Pos (x :: xs) here = inl ⋆
Pos'-to-Pos (x :: xs) (there y) = inr (Pos'-to-Pos xs y)
```

### Exercise 3.3

Using the above functions, **prove** that `Pos xs` is isomorphic to `Pos' xs`
for every list `xs`.

```agda
Pos-isomorphic-to-Pos' : {X : Type} (xs : List X) → Pos xs ≅ Pos' xs
Pos-isomorphic-to-Pos' {X} xs = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Pos xs → Pos' xs
  f x = (Pos-to-Pos' xs) x

  g : Pos' xs → Pos xs
  g = Pos'-to-Pos xs

  gf : g ∘ f ∼ id
  gf = lemma xs
    where
      lemma : (ys : List X) → (Pos'-to-Pos ys ∘ Pos-to-Pos' ys) ∼ id
      lemma (y :: ys) (inl ⋆) = refl _
      lemma (y :: ys) (inr x) = ap inr (lemma ys x) 

  fg : f ∘ g ∼ id
  fg = lemma xs
    where
      lemma : (ys : List X) → (Pos-to-Pos' ys ∘ Pos'-to-Pos ys) ∼ id
      lemma (y :: ys) here = refl _
      lemma (y :: ys) (there x) = ap there (lemma ys x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }


```

### Exercise 3.4

Yet another way to define the positions is by using `Fin (length xs)`, the
inductively defined type that has exactly `length xs`-many elements.

**Define** the map that takes a position of `xs` and gives an element of `Fin
  (length xs)`.

```agda
Pos-to-Fin-length : {X : Type} (xs : List X) → Pos xs → Fin (length xs)
Pos-to-Fin-length [] = 𝟘-elim
Pos-to-Fin-length (x :: xs) (inl ⋆) = zero
Pos-to-Fin-length (x :: xs) (inr p) = suc (Pos-to-Fin-length xs p)
```

### Exercise 3.5

**Define** the map in the other direction.

```agda
Fin-length-to-Pos : {X : Type} (xs : List X) → Fin (length xs) → Pos xs
Fin-length-to-Pos [] = Fin-0-is-empty
Fin-length-to-Pos (x :: xs) zero = inl ⋆
Fin-length-to-Pos (x :: xs) (suc p) = inr (Fin-length-to-Pos xs p)
```

### Exercise 3.6

Using the above functions, **prove** that `Pos xs` is isomorphic to `Fin (length
xs)` for every list `xs`.

```agda
Pos-isomorphic-to-Fin-length : {X : Type} (xs : List X)
                             → Pos xs ≅ Fin (length xs)
Pos-isomorphic-to-Fin-length {X} xs = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Pos xs → Fin (length xs)
  f = Pos-to-Fin-length xs

  g : Fin (length xs) → Pos xs
  g = Fin-length-to-Pos xs

  gf : g ∘ f ∼ id
  gf = lemma xs
    where
     lemma : (ys : List X) → (Fin-length-to-Pos ys ∘ Pos-to-Fin-length ys) ∼ id
     lemma (y :: ys) (inl ⋆) = refl (inl ⋆)
     lemma (y :: ys) (inr x) = ap inr (lemma ys x)

  fg : f ∘ g ∼ id
  fg = lemma xs
    where
      lemma : (ys : List X) → (Pos-to-Fin-length ys ∘ Fin-length-to-Pos ys) ∼ id
      lemma (y :: ys) zero = refl zero
      lemma (y :: ys) (suc x) = ap suc (lemma ys x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg }

```

