# Week 3 - Lab Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.lab3 where
open import prelude hiding (𝟘-nondep-elim)
```

## Part I: Propositional logic

### Section 1: Disjunction

#### Exercise I.1.1

**Complete** the following proofs involving disjunctions.

```agda
private

 ∔-introduction-left  : {A B : Type} → A → A ∔ B
 ∔-introduction-left = {!!}

 ∔-introduction-right : {A B : Type} → B → A ∔ B
 ∔-introduction-right = {!!}
```

#### Exercise I.1.2

**Complete** the proof about disjunctions.

```agda
 ∔-elimination : {A B X : Type} → (A → X) → (B → X) → (A ∔ B → X)
 ∔-elimination = {!!}
```

### Section 2: Conjunction

#### Exercise I.2.1

**Complete** the following proofs involving conjunctions.

```agda
 ×-elimination-left : {A B : Type} → A × B → A
 ×-elimination-left = {!!}

 ×-elimination-right : {A B : Type} → A × B → B
 ×-elimination-right = {!!}
```

#### Exercise I.2.2

**Prove** the following:

```agda
 ×-introduction : {A B : Type} → A → B → A × B
 ×-introduction = {!!}

 ×-introduction' : {A B X : Type} → (X → A) → (X → B) → (X → A × B)
 ×-introduction' = {!!}
```

### Section 3: Implication

#### Exercise I.3.1

**Complete** the following proofs involving implications.

```agda
 uncurry : {A B X : Type} → (A → B → X) → (A × B → X)
 uncurry = {!!}

 curry : {A B X : Type} → (A × B → X) → (A → B → X)
 curry = {!!}
```

You probably already know `curry` and `uncurry` from Haskell, but
notice how we can read them from a logical perspective: `uncurry`
says that if `A` implies that `B` implies `X`, then the conjunction of
`A` and `B` implies `X`.

#### Exercise I.3.2

**Prove** that implication is transitive.

```
 →-trans : {A B C : Type} → (A → B) → (B → C) → (A → C)
 →-trans = {!!}
```

Notice that the proof that implication is transitive is just function
composition.


### Section 4: Negation

The fact that falsity implies everything is known as the [_principle of
explosion_](https://en.wikipedia.org/wiki/Principle_of_explosion) or _ex falso
quodlibet_.

**Complete** the proof of the principle of explosion in Agda.

#### Exercise I.4.1

```agda
 𝟘-nondep-elim : {A : Type} → 𝟘 → A
 𝟘-nondep-elim = {!!}
```

#### Exercise I.4.2

**Write** two *different* proofs that show "not false" (or "the empty
type is empty").

```agda
 not-false : ¬ 𝟘
 not-false = {!!}

 not-false' : ¬ 𝟘
 not-false' = {!!}
```

#### Exercise I.4.3

Before we proceed, we introduce some convenient notation
for multiple negations.

```agda
 ¬¬ : Type → Type
 ¬¬ A = ¬ (¬ A)

 ¬¬¬ : Type → Type
 ¬¬¬ A = ¬ (¬¬ A)
```

**Complete** the proof a proposition implies its own double negation,
by first proving the more general notion `dni`.

```agda
 dni : (A R : Type) → A → ((A → R) → R)
 dni = {!!}
 
 ¬¬-introduction : {A : Type} → A → ¬¬ A
 ¬¬-introduction = {!!}
```

#### Exercise I.4.4

**Prove** that having three negations is the logically equivalent to
having a single negation.

```agda
 not-implies-not³ : {A : Type} → ¬ A → ¬¬¬ A
 not-implies-not³ = {!!}

 not³-implies-not : {A : Type} → ¬¬¬ A → ¬ A
 not³-implies-not = {!!}
```

#### Exercise I.4.5

A particular case of interest of `→-trans` is the following. The
[contrapositive](https://en.wikipedia.org/wiki/Contraposition) of an
implication `A → B` is the implication `¬ B → ¬ A`.

**Complete** the proof of contraposition.

```agda
 contraposition : {A B : Type} → (A → B) → ¬ B → ¬ A
 contraposition = {!!}
```

This can also be read as "if we have a function A → B and B is empty,
then also A must be empty".

#### Exercise I.4.6

Use `contraposition` to **complete** the following proof of double
contraposition.

```agda
 double-contrapositive : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
 double-contrapositive = {!!}
```

#### Exercise I.4.7

Use `contraposition` to **complete** the following two proofs that show
double negation is a monad.

```agda
 ¬¬-functor : {A B : Type} → (A → B) → ¬¬ A → ¬¬ B
 ¬¬-functor = {!!}

 ¬¬-kleisli : {A B : Type} → (A → ¬¬ B) → ¬¬ A → ¬¬ B
 ¬¬-kleisli = {!!}
```

### Section 5: De Morgan Laws and logical laws

The De Morgan laws cannot be proved in Agda, though some of the
implications involved in the De Morgan laws _can_ be. The following
exercises will involve proving these (and some other similar laws) for
Agda types.

#### Exercise I.5.1

**Complete** the proofs.

```agda
 de-morgan₁ : {A B : Type} → ¬ (A ∔ B) → ¬ A × ¬ B
 de-morgan₁ = {!!}

 de-morgan₂ : {A B : Type} → ¬ A ∔ ¬ B → ¬ (A × B)
 de-morgan₂ = {!!}
```

#### Exercise I.5.2

**Complete** the proofs.

```agda
 ¬-and-+-exercise₁ : {A B : Type} → ¬ A ∔ B → A → B
 ¬-and-+-exercise₁ = {!!}

 ¬-and-+-exercise₂ : {A B : Type} → ¬ A ∔ B → ¬ (A × ¬ B)
 ¬-and-+-exercise₂ = {!!}
```

#### Exercise I.5.3

If  `A ∔ B` holds and `B` is false, then `A` must hold (and vice
versa). **Compelete** the proofs of this.

#### Exercise I.5.4

**Prove** the distributivity laws for `×` and `∔`.

```agda
 distributivity₁ : {A B C : Type} → (A × B) ∔ C → (A ∔ C) × (B ∔ C)
 distributivity₁ = {!!}

 distributivity₂ : {A B C : Type} → (A ∔ B) × C → (A × C) ∔ (B × C)
 distributivity₂ = {!!}
```

#### Exercise I.5.5

Earlier, we showed that `A → ¬¬ A`; but we don't always have `¬¬ A → A`
in proofs-as-programs (this has to do with *computability theory*).
But sometimes we do. For example, if we know that `A ∔ ¬ A` holds,
then `¬¬A → A` follows.

**Prove** this fact.

```agda
 ¬¬-elim : {A : Type} → A ∔ ¬ A → ¬¬ A → A
 ¬¬-elim = {!!}
```

## Part II: Logic with quantifiers

### Section 1: Sums

#### Exercise II.1.1

**Complete** the following constructions.

```agda
 Σ-introduction : {A : Type} {B : (A → Type)}
                → (a : A) → B a → (Σ a ꞉ A , B a)
 Σ-introduction = {!!}

 Σ-to-× : {A : Type} {B : (A → Type)}
        → ((a , _) : (Σ a ꞉ A , B a)) → A × B a
 Σ-to-× = {!!}
```

#### Exercise II.1.2

**Complete** the following proof about sums over Booleans.

```agda
 Σ-on-Bool : {B : Bool → Type} → (Σ x ꞉ Bool , B x) → B true ∔ B false
 Σ-on-Bool = {!!}
```

### Section 2: Products

#### Exercise II.2.1

Complete the proof.

```agda
 Π-apply : {A : Type} {B : (A → Type)}
         → ((a : A) → B a) → (a : A) → B a
 Π-apply = {!!}
```

#### Exercise II.2.2

**Prove**  the following.

```agda
 Π-→ : {A : Type} {B C : A → Type}
     → ((a : A) → B a → C a)
     → ((a : A) → B a) → ((a : A) → C a)
 Π-→ = {!!}
```

### Section 3: Negation

#### Exercise III.3.1

**Show** that if there is no `x : X` with `A x`, then for all `x : X`
not `A x`.

```agda
not-exists-implies-forall-not : {X : Type} {A : X → Type}
                              → ¬ (Σ x ꞉ X , A x)
                              → (x : X) → ¬ A x
not-exists-implies-forall-not = {!!}
```

Also **show** that the converse also holds.

```agda
forall-not-implies-not-exists : {X : Type} {A : X → Type}
                              → ((x : X) → ¬ A x)
                              → ¬ (Σ x ꞉ X , A x)
forall-not-implies-not-exists = {!!}
```

Notice how these are particular cases of `curry` and `uncurry` from
Exercise I.3.1!
