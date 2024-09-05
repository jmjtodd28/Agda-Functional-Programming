<!--
```agda
{-# OPTIONS --without-K --safe #-}

module Fin-functions-lecture where

open import prelude
```
-->

# Isomorphism of Fin n with a Basic MLTT type

```agda
Fin' : ℕ → Type
Fin' 0       = 𝟘
Fin' (suc n) = 𝟙 ∔ Fin' n
zero' : {n : ℕ} → Fin' (suc n)
zero' = inl ⋆
suc' : {n : ℕ} → Fin' n → Fin' (suc n)
suc' = inr

example₀ : Fin' 17
example₀ = suc' (suc' (suc' zero'))

open import Fin
open import isomorphisms

Fin-isomorphism : (n : ℕ) → Fin n ≅ Fin' n
Fin-isomorphism n = record { bijection = f n ; bijectivity = f-is-bijection n }
 where
  f : (n : ℕ) → Fin n → Fin' n
  f (suc _) zero = zero'
  f (suc n) (suc k) = suc' (f n k)

  g : (n : ℕ) → Fin' n → Fin n
  g (suc n) (inl ⋆) = zero
  g (suc n) (inr x) = suc (g n x)

  gf : (n : ℕ) → g n ∘ f n ∼ id
  gf .(suc _) zero = refl zero
  gf (suc n) (suc k) = ap suc (gf n k)

  fg : (n : ℕ) → f n ∘ g n ∼ id
  fg = {!!}

  f-is-bijection : (n : ℕ) → is-bijection (f n)
  f-is-bijection n = record { inverse = g n ; η = gf n ; ε = fg n}
```

**Exercise.** Show that the type `Fin n` is isormorphic to the type `Σ k : ℕ , k < n`.
