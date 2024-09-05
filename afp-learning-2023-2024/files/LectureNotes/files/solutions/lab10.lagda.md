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
nonempty-is-nonempty' {A} leaf = ltr , rtl
 where
  ltr : nonempty leaf → nonempty' {A} leaf
  ltr (x , ())
  rtl : nonempty' {A} leaf → nonempty leaf
  rtl f = 𝟘-nondep-elim (f (refl 0))
nonempty-is-nonempty' {A} (branch x l r) = ltr , rtl
 where
  ltr : nonempty (branch x l r) → nonempty' (branch x l r)
  ltr _ ()
  rtl : nonempty' (branch x l r) → nonempty (branch x l r)
  rtl f = x , (inl (refl x))
```

## Exercise 1.2

**Prove** the following lemma about reverse and append.

```agda
reverse-++-lemma : {A : Type} (r : List A) (x : A) (l : List A)
                 → reverse r ++ [ x ] ++ reverse l
                 ≡ reverse (l ++ [ x ] ++ r)
reverse-++-lemma r x [] = refl (reverse r ++ [ x ])
reverse-++-lemma r x (y :: l)
 = reverse r ++ [ x ] ++ reverse (y :: l)
     ≡⟨ refl _ ⟩
   reverse r ++ ([ x ] ++ (reverse l ++ [ y ]))
     ≡⟨ ap (reverse r ++_) (++-assoc [ x ] (reverse l) [ y ]) ⟩
   reverse r ++ (([ x ] ++ reverse l) ++ [ y ])
     ≡⟨ sym (++-assoc (reverse r) ([ x ] ++ reverse l) [ y ]) ⟩
  (reverse r ++ [ x ] ++ reverse l) ++ [ y ]
     ≡⟨ ap (_++ [ y ]) (reverse-++-lemma r x l) ⟩
   reverse (l ++ [ x ] ++ r) ++ [ y ]
     ≡⟨ refl _ ⟩ 
   reverse ([ y ] ++ l ++ [ x ] ++ r) ∎
```

## Exercise 1.3

Use `reverse-++-lemma` to **prove** that flattening a mirrored tree is
the same as reversing a flattened tree.

```agda
flatten-mirror-is-reverse-flatten
 : {A : Type} → flatten {A} ∘ mirror ∼ reverse ∘ flatten
flatten-mirror-is-reverse-flatten leaf = refl []
flatten-mirror-is-reverse-flatten (branch x l r)
 =  flatten (mirror r) ++ [ x ] ++ flatten (mirror l)
     ≡⟨ ap (λ - → - ++ [ x ] ++ flatten (mirror l))
           (flatten-mirror-is-reverse-flatten r) ⟩
   reverse (flatten r) ++ [ x ] ++ flatten (mirror l)
     ≡⟨ ap (λ - → reverse (flatten r) ++ [ x ] ++ -)
           (flatten-mirror-is-reverse-flatten l) ⟩
   reverse (flatten r) ++ [ x ] ++ reverse (flatten l)
     ≡⟨ reverse-++-lemma (flatten r) x (flatten l) ⟩
    reverse (flatten l ++ [ x ] ++ flatten r) ∎
```

## Exercise 1.4

The function `flatten` performs an inorder traversal of the given tree.
Now **define** the functions of type `BT X → List X` that perform
preorder and postorder traversals of the given tree.

```agda
preorder  : {X : Type} → BT X → List X
preorder leaf = []
preorder (branch x l r) = x :: (preorder l ++ preorder r)

postorder : {X : Type} → BT X → List X
postorder leaf = []
postorder (branch x l r) = postorder l ++ postorder r ++ [ x ]
```

## Exercise 1.5

**Prove** that performing a preorder traversal of a tree is the same as
reversing a postorder traversal of the mirror of that tree.

*Hint:* First prove and use the lemma below.

```agda
open import solutions.lab4 using (reverse-lemma)

reverse-++-lemma' : {X : Type} (l r : List X)
                  → reverse l ++ reverse r ≡ reverse (r ++ l)
reverse-++-lemma' l [] = []-right-neutral (reverse l)
reverse-++-lemma' l (x :: r)
 = reverse l ++ (reverse r ++ [ x ])
     ≡⟨ sym (++-assoc (reverse l) (reverse r) ([ x ])) ⟩
   (reverse l ++ reverse r) ++ [ x ]
     ≡⟨ ap (_++ [ x ]) (reverse-++-lemma' l r) ⟩
   reverse (r ++ l) ++ [ x ] ∎ 

preorder-is-reverse-of-postorder-mirror
 : {X : Type} → preorder {X} ∼ reverse ∘ postorder ∘ mirror
preorder-is-reverse-of-postorder-mirror leaf
 = refl []
preorder-is-reverse-of-postorder-mirror (branch x l r)
 = x :: (preorder l ++ preorder r)
     ≡⟨ ap (x ::_) (ap₂ _++_
                     (preorder-is-reverse-of-postorder-mirror l)
                     (preorder-is-reverse-of-postorder-mirror r)) ⟩
   x :: (reverse (postorder (mirror l)))
     ++ (reverse (postorder (mirror r)))
     ≡⟨ ap (_++ reverse (postorder (mirror r)))
           (reverse-++-lemma' [ x ] (postorder (mirror l))) ⟩ 
      reverse (postorder (mirror l) ++ [ x ])
   ++ reverse (postorder (mirror r))
     ≡⟨ reverse-++-lemma'
          (postorder (mirror l) ++ [ x ]) (postorder (mirror r)) ⟩
   reverse (postorder (mirror r) ++ postorder (mirror l) ++ [ x ])  ∎ 
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
 insert'-preserves-all-smaller y x leaf   y<x b = y<x , ⋆ , ⋆
 insert'-preserves-all-smaller y x (branch z l r) y<x (x<z , sl , sr)
  = γ (trichotomy z y)
  where
   γ : (trich : Trichotomy z y)
     → all-smaller (insert'-branch y z l r trich) x
   γ (inl      z<y )
    = x<z , sl , insert'-preserves-all-smaller y x r y<x sr
   γ (inr (inl (refl _))) = x<z , sl , sr
   γ (inr (inr z>y))
    = x<z , insert'-preserves-all-smaller y x l y<x sl , sr 

 insert'-preserves-all-bigger : (y x : X) (t : BT X)
                              → y > x
                              → all-bigger t x
                              → all-bigger (insert' y t) x
 insert'-preserves-all-bigger y x leaf   y>x b = y>x , ⋆ , ⋆
 insert'-preserves-all-bigger y x (branch z l r) y>x (x<z , bl , br)
  = γ (trichotomy z y)
  where
   γ : (trich : Trichotomy z y)
     → all-bigger (insert'-branch y z l r trich) x
   γ (inl      z<y )
    = x<z , bl , insert'-preserves-all-bigger y x r y>x br
   γ (inr (inl (refl _))) = x<z , bl , br
   γ (inr (inr z>y))
    = x<z , insert'-preserves-all-bigger y x l y>x bl , br    
```

## Exercise 2.2

**Prove** that `all-smaller` and `all-bigger` are decidable properties.

```agda
 all-smaller-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-smaller t x)
 all-smaller-is-decidable leaf   y = 𝟙-is-decidable
 all-smaller-is-decidable (branch x l r) y =
    ×-preserves-decidability (<-is-decidable x y)
   (×-preserves-decidability (all-smaller-is-decidable l y)
                             (all-smaller-is-decidable r y))

 all-bigger-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-bigger t x)
 all-bigger-is-decidable leaf   y = 𝟙-is-decidable
 all-bigger-is-decidable (branch x l r) y =
    ×-preserves-decidability (<-is-decidable y x)
   (×-preserves-decidability (all-bigger-is-decidable l y)
                             (all-bigger-is-decidable r y))
```

Hence, prove that it is decidable whether or not a `BT X` is a BST.

```agda
 being-bst-is-decidable : (t : BT X) → is-decidable (is-bst t)
 being-bst-is-decidable leaf   = 𝟙-is-decidable
 being-bst-is-decidable (branch x l r) =
   ×-preserves-decidability (all-smaller-is-decidable l x)
  (×-preserves-decidability (all-bigger-is-decidable r x)
  (×-preserves-decidability (being-bst-is-decidable l)
                            (being-bst-is-decidable r)))
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
   γ (inl y<x) x∈ₛt
    = ap (branch y l) (insert-same-tree-property x r ir x∈ₛt)
   γ (inr (inl y≡x)) x∈ₛt
    = refl (branch y l r)
   γ (inr (inr x<y)) x∈ₛt
    = ap (λ - → branch y - r) (insert-same-tree-property x l il x∈ₛt)
```

## Exercise 2.5

In the lecture, we prove that the efficient membership implies the
original membership on BSTs.

Now, **prove** the other direction of this.

```agda
 all-smaller-means-smaller
  : (y x : X) (l : BT X) → all-smaller l x → y ∈ l → y < x
 all-smaller-means-smaller
  y x (branch z l r) (z<x , sl , sr) (inl      y≡z )
  = transport (_< x) (sym y≡z) z<x
 all-smaller-means-smaller
  y x (branch z l r) (z<x , sl , sr) (inr (inl y∈l))
  = all-smaller-means-smaller y x l sl y∈l
 all-smaller-means-smaller
  y x (branch z l r) (z<x , sl , sr) (inr (inr y∈r))
  = all-smaller-means-smaller y x r sr y∈r

 all-bigger-means-bigger
  : (y x : X) (r : BT X) → all-bigger r x → y ∈ r → y > x
 all-bigger-means-bigger
  y x (branch z l r) (z>x , bl , br) (inl      y≡z )
  = transport (_> x) (sym y≡z) z>x
 all-bigger-means-bigger
  y x (branch z l r) (z>x , bl , br) (inr (inl y∈l))
  = all-bigger-means-bigger y x l bl y∈l
 all-bigger-means-bigger
  y x (branch z l r) (z>x , bl , br) (inr (inr y∈r))
  = all-bigger-means-bigger y x r br y∈r
 
 membership'-implies-membership : (y : X) (t : BT X) (i : is-bst t)
                                → y ∈ₛ' (t , i) → y ∈ₛ (t , i)
 membership'-implies-membership y t@(branch x l r) i@(s , b , il , ir)
  = γ (trichotomy x y)
  where
   γ : (trich : Trichotomy x y)
     → y ∈ₛ' (t , i)
     → ∈ₛ-branch y x l r trich
   γ (inl      x<y ) (inl      y≡x )
    = 𝟘-nondep-elim (irreflexive' x y (sym y≡x) x<y)
   γ (inl      x<y ) (inr (inl y∈l))
    = 𝟘-nondep-elim (antisymmetric x y x<y
        (all-smaller-means-smaller y x l s y∈l))
   γ (inl      x<y ) (inr (inr y∈r))
    = membership'-implies-membership y r ir y∈r
   γ (inr (inl x≡y)) _ = ⋆
   γ (inr (inr x>y)) (inl      y≡x )
    = 𝟘-nondep-elim (irreflexive' y x y≡x x>y)
   γ (inr (inr x>y)) (inr (inl y∈l))
    = membership'-implies-membership y l il y∈l
   γ (inr (inr x>y)) (inr (inr y∈r))
    = 𝟘-nondep-elim (antisymmetric y x x>y
        (all-bigger-means-bigger y x r b y∈r))
```

## Exercise 2.6

**Prove** that if we insert an item into a binary search tree, the
size either remains the same or increases by one.

```agda
 insert-size-property : (x : X) (t : BT X) (i : is-bst t)
                      → (size (fst (insert x (t , i))) ≡ size t)
                      ∔ (size (fst (insert x (t , i))) ≡ size t + 1)
 insert-size-property x leaf   i = inr (refl 1)
 insert-size-property x (branch y l r) (s , b , il , ir)
  = γ (trichotomy y x)
  where
   γ : (trich : Trichotomy y x)
     → (size (insert'-branch x y l r trich) ≡ suc (size l + size r))
     ∔ (size (insert'-branch x y l r trich) ≡ suc ((size l + size r) + 1))
   γ (inl y<x)
    = ∔-nondep-elim (λ e → inl (ap (λ - → suc (size l + -)) e))
                    (λ e → inr (ap suc
                      (trans (ap (size l +_) e)
                        (sym (+-assoc (size l) (size r) 1)))))
                    (insert-size-property x r ir)
   γ (inr (inl y≡x)) = inl (refl _)
   γ (inr (inr y>x))
    = ∔-nondep-elim (λ e → inl (ap (λ - → suc (- + size r)) e))
                    (λ e → inr (ap suc
                      (trans (ap (_+ size r) e)
                        (trans (ap (_+ size r) (+-comm (size l) 1))
                          (+-comm 1 (size l + size r))))))
                    (insert-size-property x l il)
```

## Exercise 2.7

**Prove** that if an item is a member of a binary search tree that it
is inserted into.

*Hint:* You may need to prove some additional lemmas about
`∈ₛ-branch`.

```agda
 ∈ₛ-branch-left : (x y : X) (l r : BT X)
                → (trich : Trichotomy y x)
                → y > x
                → x ∈ₛ-bst l
                → ∈ₛ-branch x y l r trich
 ∈ₛ-branch-left x y l r (inl y<x) y>x x∈ₛr
  = 𝟘-nondep-elim (antisymmetric y x y<x y>x)
 ∈ₛ-branch-left x y l r (inr (inl y≡x)) y>x x∈ₛr
  = 𝟘-nondep-elim (irreflexive' x y (sym y≡x) y>x)
 ∈ₛ-branch-left x y l r (inr (inr y>x)) _ x∈ₛl
  = x∈ₛl 

 ∈ₛ-branch-middle : (x y : X) (l r : BT X)
                  → (trich : Trichotomy y x)
                  → y ≡ x
                  → ∈ₛ-branch x y l r trich
 ∈ₛ-branch-middle x x l r (inl y<x) (refl x)
  = 𝟘-nondep-elim (irreflexive x y<x)
 ∈ₛ-branch-middle x x l r (inr (inl y≡x)) (refl x)
  = ⋆
 ∈ₛ-branch-middle x x l r (inr (inr y>x)) (refl x)
  = 𝟘-nondep-elim (irreflexive x y>x)

 ∈ₛ-branch-right : (x y : X) (l r : BT X)
                 → (trich : Trichotomy y x)
                 → y < x
                 → x ∈ₛ-bst r
                 → ∈ₛ-branch x y l r trich
 ∈ₛ-branch-right x y l r (inl y<x) _ x∈ₛr
  = x∈ₛr
 ∈ₛ-branch-right x y l r (inr (inl y≡x)) y<x x∈ₛr
  = 𝟘-nondep-elim (irreflexive' y x y≡x y<x)
 ∈ₛ-branch-right x y l r (inr (inr y>x)) y<x x∈ₛr
  = 𝟘-nondep-elim (antisymmetric y x y<x y>x)
  
 insert-membership-property : (x : X) (t : BT X) (i : is-bst t)  
                            → x ∈ₛ insert x (t , i)
 insert-membership-property x leaf i = γ (trichotomy x x)
  where
   γ : (trich : Trichotomy x x) → ∈ₛ-branch x x leaf leaf trich
   γ (inl x<x) = irreflexive x x<x
   γ (inr (inl x≡x)) = ⋆
   γ (inr (inr x<x)) = irreflexive x x<x
 insert-membership-property x (branch y l r) (s , b , il , ir)
  = γ (trichotomy y x)
  where
   γ : (trich : Trichotomy y x)
     → x ∈ₛ-bst insert'-branch x y l r trich
   γ (inl y<x)
    = ∈ₛ-branch-right x y l (insert' x r) (trichotomy y x)
        y<x (insert-membership-property x r ir)
   γ (inr (inl y≡x))
    = ∈ₛ-branch-middle x y l r (trichotomy y x) y≡x
   γ (inr (inr y>x))
    = ∈ₛ-branch-left x y (insert' x l) r (trichotomy y x)
        y>x (insert-membership-property x l il)
```

## Exercise 2.6

**Prove** that if an element `y` is in the tree `insert x t`, then `y`
is either equal to `x` or is in the tree `t`.

*Hint:* You may need to prove some additional lemmas about
`∈ₛ-branch`.

```agda


 ∈ₛ-branch-left' : (x y : X) (l r : BT X)
                 → (trich : Trichotomy y x)
                 → y > x
                 → ∈ₛ-branch x y l r trich
                 → x ∈ₛ-bst l
 ∈ₛ-branch-left' x y l r (inl y<x) y>x x∈ₛl
  = 𝟘-nondep-elim (antisymmetric y x y<x y>x)
 ∈ₛ-branch-left' x y l r (inr (inl y≡x)) y>x x∈ₛl
  = 𝟘-nondep-elim (irreflexive' x y (sym y≡x) y>x) 
 ∈ₛ-branch-left' x y l r (inr (inr y>x)) _ x∈ₛl
  = x∈ₛl

 ∈ₛ-branch-right' : (x y : X) (l r : BT X)
                  → (trich : Trichotomy y x)
                  → y < x
                  → ∈ₛ-branch x y l r trich
                  → x ∈ₛ-bst r
 ∈ₛ-branch-right' x y l r (inl y<x) _ x∈ₛr
  = x∈ₛr
 ∈ₛ-branch-right' x y l r (inr (inl y≡x)) y<x x∈ₛr
  = 𝟘-nondep-elim (irreflexive' y x y≡x y<x)
 ∈ₛ-branch-right' x y l r (inr (inr y>x)) y<x x∈ₛr
  = 𝟘-nondep-elim (antisymmetric y x y<x y>x)

 membership-insert-property : (x y : X) (t : BT X) (i : is-bst t)
                            → y ∈ₛ insert x (t , i)
                            → (y ≡ x) ∔ (y ∈ₛ (t , i))
 membership-insert-property x y leaf i y∈ₛt
  = γ (trichotomy x y) y∈ₛt
  where
   γ : (trich : (x < y) ∔ (x ≡ y) ∔ (x > y))
     → ∈ₛ-branch y x leaf leaf trich
     → (y ≡ x) ∔ 𝟘
   γ (inl x<y) ()
   γ (inr (inl x≡y)) ⋆ = inl (sym x≡y)
   γ (inr (inr x>y)) ()
 membership-insert-property x y (branch z l r) (s , b , il , ir)
  = γ (trichotomy z x) (trichotomy z y)
  where
   γ : (trich-zx : (z < x) ∔ (z ≡ x) ∔ (z > x))
     → (trich-zy : (z < y) ∔ (z ≡ y) ∔ (z > y))
     → y ∈ₛ-bst insert'-branch x z l r trich-zx
     → (y ≡ x) ∔ ∈ₛ-branch y z l r trich-zy
   γ (inl z<x) (inl z<y) y∈ₛt
    = membership-insert-property x y r ir
        (∈ₛ-branch-right' y z l (insert' x r) (trichotomy z y) z<y y∈ₛt)
   γ (inl z<x) (inr (inr z>y)) y∈ₛt
    = inr (∈ₛ-branch-left' y z l (insert' x r) (trichotomy z y) z>y y∈ₛt) 
   γ (inr (inl (refl _))) (inl z<y) y∈ₛt
    = inr (∈ₛ-branch-right' y z l r (trichotomy z y) z<y y∈ₛt)
   γ (inr (inl (refl _))) (inr (inr z>y)) y∈ₛt
    = inr (∈ₛ-branch-left' y z l r (trichotomy z y) z>y y∈ₛt)
   γ (inr (inr z>x)) (inl z<y) y∈ₛt
    = inr (∈ₛ-branch-right' y z (insert' x l) r (trichotomy z y) z<y y∈ₛt)
   γ (inr (inr z>x)) (inr (inr z>y)) y∈ₛt
    = membership-insert-property x y l il
        (∈ₛ-branch-left' y z (insert' x l) r (trichotomy z y) z>y y∈ₛt)
   γ (inl z<x) (inr (inl (refl _))) y∈ₛt = inr ⋆
   γ (inr (inl (refl _))) (inr (inl (refl _))) y∈ₛt = inr ⋆
   γ (inr (inr z>x)) (inr (inl (refl _))) y∈ₛt = inr ⋆
```
