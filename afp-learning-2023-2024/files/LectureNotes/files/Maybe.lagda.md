<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Maybe where

open import general-notation
open import products
open import identity-type
```
-->
# The `Maybe` type constructor

```agda

data Maybe (X : Type) : Type where
  nothing : Maybe X
  just    : X → Maybe X
```

## Elimination principle

```agda
Maybe-elim : {X : Type} (A : Maybe X → Type)
           → A nothing
           → ((x : X) → A (just x))
           → (m : Maybe X) → A m
Maybe-elim A a f nothing  = a
Maybe-elim A a f (just x) = f x
```
In terms of functional programming, this says that using an element `a : A nothing` and a dependent function `f : (x : X) → A (just x)`, we can define a dependent function of type `(m : Maybe X) → A m`, by cases on whether `m` is `nothing` or `just x`.

In terms of logic, the elimination principle says that in order to prove that "for all `m : Maybe X`, the proposition `A m` holds" it is enough to prove that `A nothing` holds and that for all `x : X`, the proposition `A (just x)` holds.

## Non-dependent version

It is a special case of the dependent version:
```agda
Maybe-nondep-elim : {X A : Type}
                  → A
                  → (X → A)
                  → Maybe X → A
Maybe-nondep-elim {X} {A} = Maybe-elim (λ _ → A)
```

## Isomorphism with a Basic MLTT type

We now show that there is an [isomorphism](isomorphisms.lagda.md) of the type `Maybe X` with a type in basic Martin-Löf Type Theory, so that, strictly speaking, we don't need to include `Maybe` in our repertoire of Agda definitions. Nevertheless, in practice, it is convenient to include it.
```agda
open import unit-type
open import binary-sums
open import isomorphisms

Maybe-isomorphism : (X : Type) → Maybe X ≅ 𝟙 ∔ X
Maybe-isomorphism X = record { bijection = f ; bijectivity = f-is-bijection }
 where
  f : Maybe X → 𝟙 ∔ X
  f nothing  = inl ⋆
  f (just x) = inr x

  g : 𝟙 ∔ X → Maybe X
  g (inl ⋆) = nothing
  g (inr x) = just x

  gf : g ∘ f ∼ id
  gf nothing  = refl nothing
  gf (just x) = refl (just x)

  fg : f ∘ g ∼ id
  fg (inl ⋆) = refl (inl ⋆)
  fg (inr x) = refl (inr x)

  f-is-bijection : is-bijection f
  f-is-bijection = record { inverse = g ; η = gf ; ε = fg}
```

## The monad structure and laws

We will define later, in Agda, what a monad is. But before knowing what a monad is, it is possible to define the monad structure. We do this using the non-dependent eliminator. We define this within a submodule. Note that the things within the submodule must be indented.
```agda
module Maybe-Monad where

 return : {X : Type} → X → Maybe X
 return = just

 extend : {X Y : Type} → (X → Maybe Y) → Maybe X → Maybe Y
 extend = Maybe-nondep-elim nothing

 _>>=_ : {X Y : Type} → Maybe X → (X → Maybe Y) → Maybe Y
 xm >>= f = extend f xm
```
As we will see later, the monad structure consists of `return` and `>>=`. Another way to present a monad is with `return`, `map` and `join`:
```agda

 map : {X Y : Type} → (X → Y) → Maybe X → Maybe Y
 map f = extend (return ∘ f)

 join : {X : Type} → Maybe (Maybe X) → Maybe X
 join = extend id
```
Here `∘` is function composition and `id` is the identity function.

The following function is useful when making monadic computations with `Maybe`:
```agda
 _orElse_ : {A : Type} → Maybe A → Maybe A → Maybe A
 nothing orElse n = n
 (just x) orElse n = just x
```

Here are some facts about these functions, which could have been used as definitions by pattern matching, if we wished:
```agda
 extend-nothing : {X Y : Type} (f : X → Maybe Y) → extend f nothing ≡ nothing
 extend-nothing f = refl nothing

 extend-just : {X Y : Type} (f : X → Maybe Y) (x : X) → extend f (just x) ≡ f x
 extend-just f x = refl (f x)

 map-nothing : {X Y : Type} (f : X → Y) → map f nothing ≡ nothing
 map-nothing f = refl nothing

 map-just : {X Y : Type} (f : X → Y) (x : X) → map f (just x) ≡ just (f x)
 map-just f x = refl (just (f x))

 join-nothing : {X : Type} → join nothing ≡ nothing {X}
 join-nothing = refl nothing

 join-just : {X : Type} (m : Maybe X) → join (just m) ≡ m
 join-just m = refl m
```
Notice that we wrote `nothing {X}` because Agda can't infer, in this case, which type we meant for `nothing`.

If we had defined `map` and `join` first, we could have defined `extend` from them using the following fact:
```agda
 >>=-in-terms-of-map-and-join : {X Y : Type} (f : X → Maybe Y) (m : Maybe X)
                              →  m >>= f ≡ join (map f m)
 >>=-in-terms-of-map-and-join f nothing  = refl nothing
 >>=-in-terms-of-map-and-join f (just x) = refl (f x)
```

We can also prove the monad laws before we know what a monad is:
```agda
 left-identity : {X Y : Type} (f : X → Maybe X) (x : X) → return x >>= f ≡ f x
 left-identity f x = refl (f x)

 right-identity : {X : Type} (m : Maybe X) → m >>= return ≡ m
 right-identity nothing  = refl nothing
 right-identity (just x) = refl (just x)

 associativity : {X Y Z : Type} (f : X → Maybe Y) (g : Y → Maybe Z) (m : Maybe X)
               → (m >>= f) >>= g ≡ m >>= (λ x → f x >>= g)
 associativity f g nothing  = refl nothing
 associativity f g (just x) = refl (f x >>= g)
```
The monad laws can be alternatively expressed in terms of `return`, `map` and `join`.
This is the end of the submodule. Agda uses indentation to know this.
