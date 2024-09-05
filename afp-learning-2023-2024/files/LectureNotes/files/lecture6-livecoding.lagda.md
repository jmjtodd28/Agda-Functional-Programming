<!--
```agda
{-# OPTIONS --without-K --safe #-}

module lecture6-livecoding where

open import prelude
open import negation
open import List-functions
open import natural-numbers-functions hiding (_≤_ ; suc-reflects-≤)
```
-->

Revision lecture

```agda

map-length : {X Y : Type} (xs : List X) (f : X → Y)
           → length (map f xs) ≡ length xs
map-length []        f = refl 0
map-length (x :: xs) f = goal
 where
  IH : length (map f xs) ≡ length xs
  IH = map-length xs f
  goal : suc (length (map f xs)) ≡ suc (length xs)
  goal = ap suc IH

map-length' : {X Y : Type} (xs : List X) (f : X → Y)
           → length (map f xs) ≡ length xs
map-length' []        f = refl 0
map-length' (x :: xs) f = ap suc (map-length' xs f)

map-length'' : {X Y : Type} (xs : List X) (f : X → Y)
           → length (map f xs) ≡ length xs
map-length'' []        f = refl 0
map-length'' (x :: xs) f =
 length (map f (x :: xs)) ≡⟨ refl _ ⟩   -- a
 suc (length (map f xs))  ≡⟨ ap suc (map-length'' xs f) ⟩ --b
 suc (length xs)          ≡⟨ refl _ ⟩ -- c
 length (x :: xs)         ∎ -- d

example₁ : {X : Type} (a b c d e : X)
         → a ≡ b
         → b ≡ c
         → c ≡ d
         → d ≡ e
-------------------------------------
         → a ≡ e
example₁ a b c d e p q r s = trans p (trans q (trans r s))

example₂ : {X : Type} (a b c d e : X)
         → a ≡ b
         → b ≡ c
         → c ≡ d
         → d ≡ e
-------------------------------------
         → a ≡ e
example₂ a b c d e p q r s =
 a ≡⟨ p ⟩
 b ≡⟨ q ⟩
 c ≡⟨ r ⟩
 d ≡⟨ s ⟩
 e ∎

length-++ : {X : Type} (xs ys : List X)
          → length (xs ++ ys) ≡ length xs + length ys
length-++ []        ys = refl _
length-++ (x :: xs) ys = ap suc (length-++ xs ys)

fergus-lemma : {X : Type} (xs : List X) (y : X)
             → length (xs ++ [ y ]) ≡ suc (length xs)
fergus-lemma [] x = refl 1
fergus-lemma (x :: xs) y = ap suc (fergus-lemma xs y)

reverse-preserves-length : {X : Type} (xs : List X)
                         → length (reverse xs) ≡ length xs
reverse-preserves-length []        = refl 0
reverse-preserves-length (x :: xs) =
 length (reverse (x :: xs))         ≡⟨ refl _ ⟩
 length (reverse xs ++ [ x ])       ≡⟨ length-++ (reverse xs) [ x ] ⟩
 length (reverse xs) + length [ x ] ≡⟨ refl _ ⟩
 length (reverse xs) + 1            ≡⟨ +-comm (length (reverse xs)) 1 ⟩
 suc (length (reverse xs))          ≡⟨ ap suc (reverse-preserves-length xs) ⟩
 suc (length xs)                    ≡⟨ refl _ ⟩
 length (x :: xs)                   ∎

data _≤_ : ℕ → ℕ → Type where
 0-≤   : {y : ℕ} → 0 ≤ y
 suc-≤ : {x y : ℕ} → x ≤ y → suc x ≤ suc y

ex₁ : 3 ≤ 7
ex₁ = suc-≤ (suc-≤ (suc-≤ 0-≤))

ex₂ : 4 ≤ 8
ex₂ = suc-≤ ex₁

filter : {X : Type} → (X → Bool) → List X → List X
filter p []        = []
filter p (x :: xs) = if p x then x :: filter p xs else filter p xs

trans-≤ : {x y z : ℕ} → x ≤ y → y ≤ z → x ≤ z
trans-≤ = {!!}

consec : (x : ℕ) → x ≤ suc x
consec = {!!}

filter-length : {X : Type} (p : X → Bool) (xs : List X)
              → length (filter p xs) ≤ length xs
filter-length p [] = 0-≤
filter-length p (x :: xs) with p x
filter-length p (x :: xs) | true = suc-≤ (filter-length p xs)
filter-length p (x :: xs) | false = trans-≤
                                     (filter-length p xs)
                                     (consec (length xs))

```
