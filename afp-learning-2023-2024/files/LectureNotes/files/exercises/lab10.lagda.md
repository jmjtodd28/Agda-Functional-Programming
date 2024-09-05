# Week 10 - Lab Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module exercises.lab10 where

open import prelude
open import strict-total-order
open import decidability
open import natural-numbers-functions
open import List-functions

open import BST
 hiding (nonempty-is-nonempty'
       ; reverse-++-lemma
       ; flatten-mirror-is-reverse-flatten)
```

# Part 1 - Binary Trees

## Exercise 1.1

**Prove** that the two definitions of nonemptiness are logically
equivalent.

```agda
nonempty-is-nonempty' : {A : Type} (t : BT A)
                      → nonempty t ⇔ nonempty' t
nonempty-is-nonempty' {A} t = {!!}
```

## Exercise 1.2

**Prove** the following lemma about reverse and append.

```agda
reverse-++-lemma : {A : Type} (r : List A) (x : A) (l : List A)
                 → reverse r ++ [ x ] ++ reverse l
                 ≡ reverse (l ++ [ x ] ++ r)
reverse-++-lemma r x l = {!!}
```

## Exercise 1.3

Use `reverse-++-lemma` to **prove** that flattening a mirrored tree is
the same as reversing a flattened tree.

```agda
flatten-mirror-is-reverse-flatten
 : {A : Type} → flatten {A} ∘ mirror ∼ reverse ∘ flatten
flatten-mirror-is-reverse-flatten t = {!!}
```

## Exercise 1.4

The function `flatten` performs an inorder traversal of the given tree.
Now **define** the functions of type `BT X → List X` that perform
preorder and postorder traversals of the given tree.

```agda
preorder  : {X : Type} → BT X → List X
preorder = {!!}

postorder : {X : Type} → BT X → List X
postorder = {!!}
```

## Exercise 1.5

**Prove** that performing a preorder traversal of a tree is the same as
reversing a postorder traversal of the mirror of that tree.

*Hint:* First prove and use the lemma below.

```agda
open import solutions.lab4 using (reverse-lemma)

reverse-++-lemma' : {X : Type} (l r : List X)
                  → reverse l ++ reverse r ≡ reverse (r ++ l)
reverse-++-lemma' = {!!}

preorder-is-reverse-of-postorder-mirror
 : {X : Type} → preorder {X} ∼ reverse ∘ postorder ∘ mirror
preorder-is-reverse-of-postorder-mirror = {!!}
```

# Part 2 - Binary Search Trees

```agda
module _ (X : Type) (S : StrictTotalOrder X) where

 open StrictTotalOrder S
 open BST.first-approach X S
  using (all-smaller ; all-bigger
       ; is-bst
       ; Trichotomy
       ; _∈ₛ'_ ; _∈ₛ-bst_ ; ∈ₛ-branch ;_∈ₛ_
       ; insert' ; insert'-branch ; insert)
```

## Exercise 2.1

**Prove** that `insert' : X → BT X → BT X` preserves `all-smaller` and
`all-bigger`.

```agda
 insert'-preserves-all-smaller : (y x : X) (t : BT X)
                               → y < x
                               → all-smaller t x
                               → all-smaller (insert' y t) x
 insert'-preserves-all-smaller = {!!}

 insert'-preserves-all-bigger : (y x : X) (t : BT X)
                              → y > x
                              → all-bigger t x
                              → all-bigger (insert' y t) x
 insert'-preserves-all-bigger = {!!}
```

## Exercise 2.2

**Prove** that `all-smaller` and `all-bigger` are decidable properties.

```agda
 all-smaller-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-smaller t x)
 all-smaller-is-decidable = {!!}

 all-bigger-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-bigger t x)
 all-bigger-is-decidable = {!!}
```

Hence, prove that it is decidable whether or not a `BT X` is a BST.

```agda
 being-bst-is-decidable : (t : BT X) → is-decidable (is-bst t)
 being-bst-is-decidable = {!!}
```

## Exercise 2.3

**Prove** that if we insert an item into a BST that is already in that
tree, then the resulting tree is identical to the original tree.

*Hint:* Use a proof of trichotomy! We have filled in the structure for
you.

```agda
 insert-same-tree-property : (x : X) (t : BT X) (i : is-bst t)
                           → x ∈ₛ (t , i)
                           → fst (insert x (t , i)) ≡ t
 insert-same-tree-property x (branch y l r) (s , b , il , ir)
  = γ (trichotomy y x)
  where
   γ : (trich : Trichotomy y x)
     → ∈ₛ-branch x y l r trich
     → insert'-branch x y l r trich ≡ branch y l r
   γ (inl      y<x)  x∈ₛt = {!!}
   γ (inr (inl y≡x)) x∈ₛt = {!!}
   γ (inr (inr x<y)) x∈ₛt = {!!}
```

## Exercise 2.5

In the lecture, we prove that the efficient membership implies the
original membership on BSTs.

Now, **prove** the other direction of this.

```agda
 membership'-implies-membership : (y : X) (t : BT X) (i : is-bst t)
                                → y ∈ₛ' (t , i) → y ∈ₛ (t , i)
 membership'-implies-membership = ?
```

## Exercise 2.6

**Prove** that if we insert an item into a binary search tree, the
size either remains the same or increases by one.

```agda
 insert-size-property : (x : X) (t : BT X) (i : is-bst t)
                      → (size (fst (insert x (t , i))) ≡ size t)
                      ∔ (size (fst (insert x (t , i))) ≡ size t + 1)
 insert-size-property = {!!}
```

## Exercise 2.7

**Prove** that if an item is a member of a binary search tree that it
is inserted into.

*Hint:* You may need to prove some additional lemmas about
`∈ₛ-branch`.

```agda
 insert-membership-property : (x : X) (t : BT X) (i : is-bst t)  
                            → x ∈ₛ insert x (t , i)
 insert-membership-property = {!!}
```

## Exercise 2.6

**Prove** that if an element `y` is in the tree `insert x t`, then `y`
is either equal to `x` or is in the tree `t`.

*Hint:* You may need to prove some additional lemmas about
`∈ₛ-branch`.

```agda
 membership-insert-property : (x y : X) (t : BT X) (i : is-bst t)
                            → y ∈ₛ insert x (t , i)
                            → (y ≡ x) ∔ (y ∈ₛ (t , i))
 membership-insert-property = {!!}
```

# Bonus Exercise (Very, very hard.)

**Prove** that flattening a BST results in a sorted list.

```agda
 flattened-BST-is-sorted : (t : BT X) → is-bst t → Sorted S (flatten t)
 flattened-BST-is-sorted = {!!}
```
