<!--
```agda
{-# OPTIONS --without-K --safe #-}

module decidability-rewrite where

open import prelude
open import negation

```
-->


```agda

is-decidable : Type → Type
is-decidable A = A ∔ ¬ A

map-decidable : {A B : Type} → (A → B) → (B → A) → is-decidable A → is-decidable B
map-decidable x f (inl a) = inl (x a)
map-decidable x f (inr ¬a) = inr (λ z → ¬a (f z))

map-decidable-corollary : {A B : Type} → (A ⇔ B) → (is-decidable A ⇔ is-decidable B)
map-decidable-corollary (f , g) = (map-decidable f g) , map-decidable g f

pointed-types-are-decidable : {A : Type} → A → is-decidable A
pointed-types-are-decidable x = inl x


empty-types-are-decidable : {A : Type} → ¬ A → is-decidable A
empty-types-are-decidable x = inr x

𝟙-is-decidable : is-decidable 𝟙
𝟙-is-decidable = inl ⋆

𝟘-is-decidable : is-decidable 𝟘
𝟘-is-decidable = empty-types-are-decidable 𝟘-is-empty

∔-preserves-decidability : {A B : Type}
                         → is-decidable A
                         → is-decidable B
                         → is-decidable (A ∔ B)
∔-preserves-decidability (inl x) (inl b) = inl (inl x)
∔-preserves-decidability (inl x) (inr b) = inl (inl x)
∔-preserves-decidability (inr x) (inl b) = inl (inr b)
∔-preserves-decidability (inr x) (inr b) = inr (∔-nondep-elim x b) 

```
