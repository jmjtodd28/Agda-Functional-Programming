# Week 10 - Lab Sheet

```agda
{-# OPTIONS --without-K --safe #-}

module lab10copy where

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
nonempty-is-nonempty' {A} leaf = l , r
  where
   l : nonempty leaf → nonempty' {A} leaf
   l () x

   r : nonempty' {A} leaf → nonempty leaf
   r f = 𝟘-elim (f (refl zero) ) , f (refl zero)
nonempty-is-nonempty' {A} (branch x l r) = left , right
  where
    left : nonempty (branch x l r) → nonempty' (branch x l r)
    left x ()

    right : nonempty' (branch x l r) → nonempty (branch x l r)
    right y = x , inl (refl x)

nonempty'-is-nonempty : {A : Type} (t : BT A)
                      → nonempty' t ⇔ nonempty t
nonempty'-is-nonempty {A} leaf = left , right
  where
    left : nonempty' {A} leaf → nonempty leaf
    left x = 𝟘-elim (x (refl 0)) , x (refl 0)

    right : nonempty leaf → nonempty' {A} leaf
    right () e
nonempty'-is-nonempty (branch x l r) = left , right
  where
    left : nonempty' (branch x l r) → nonempty (branch x l r)
    left e = x , inl (refl x)

    right : nonempty (branch x l r) → nonempty' (branch x l r)
    right (y , f) ()

```

## Exercise 1.2

**Prove** the following lemma about reverse and append.

```agda

mirror-is-involutive' : {A : Type} → mirror ∘ mirror ∼ id {BT A}
mirror-is-involutive' leaf = refl leaf
mirror-is-involutive' (branch x l r) = 
 branch x (mirror (mirror l)) (mirror (mirror r))
   ≡⟨ ap (λ z → branch x z (mirror (mirror r))) (mirror-is-involutive' l) ⟩
 branch x l (mirror (mirror r))
   ≡⟨ ap (λ z → branch x l z) (mirror-is-involutive' r) ⟩
 branch x l r ∎



reverse-++-lemma : {A : Type} (r : List A) (x : A) (l : List A)
                 → reverse r ++ [ x ] ++ reverse l
                 ≡ reverse (l ++ [ x ] ++ r)
reverse-++-lemma r x [] = refl _
reverse-++-lemma r x (l :: ls) = 
 reverse r ++ (x :: reverse ls ++ [ l ])     ≡⟨ sym (++-assoc (reverse r) ([ x ] ++ reverse ls) [ l ]) ⟩
 (reverse r ++ [ x ] ++ reverse ls) ++ [ l ] ≡⟨ ap (_++ [ l ]) (reverse-++-lemma r x ls) ⟩
 reverse (ls ++ (x :: r)) ++ [ l ]           ∎


```

## Exercise 1.3

Use `reverse-++-lemma` to **prove** that flattening a mirrored tree is
the same as reversing a flattened tree.

```agda
flatten-mirror-is-reverse-flatten
 : {A : Type} → flatten {A} ∘ mirror ∼ reverse ∘ flatten
flatten-mirror-is-reverse-flatten leaf = refl []
flatten-mirror-is-reverse-flatten (branch x l r) = 
 flatten (mirror r) ++ (x :: flatten (mirror l))
   ≡⟨ ap (λ t → flatten (mirror r) ++ (x :: t)) (flatten-mirror-is-reverse-flatten l) ⟩
 flatten (mirror r) ++ (x :: reverse (flatten l))
   ≡⟨ ap (λ t → t ++ (x :: reverse (flatten l))) (flatten-mirror-is-reverse-flatten r) ⟩
 reverse (flatten r) ++ (x :: reverse (flatten l))
   ≡⟨ reverse-++-lemma (flatten r) x (flatten l) ⟩
 reverse (flatten l ++ (x :: flatten r)) ∎

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
reverse-++-lemma' l (x :: r) =
 reverse l ++ reverse r ++ [ x ] ≡⟨ sym (++-assoc (reverse l) (reverse r) [ x ]) ⟩
 (reverse l ++ reverse r) ++ [ x ] ≡⟨ ap (_++ [ x ]) (reverse-++-lemma' l r) ⟩
 reverse (r ++ l) ++ [ x ] ∎

preorder-is-reverse-of-postorder-mirror
 : {X : Type} → preorder {X} ∼ reverse ∘ postorder ∘ mirror
preorder-is-reverse-of-postorder-mirror leaf = refl []
preorder-is-reverse-of-postorder-mirror (branch x l r) = 
 x :: preorder l ++ preorder r
   ≡⟨ ap (λ t → x :: t ++ preorder r) (preorder-is-reverse-of-postorder-mirror l) ⟩
 x :: (reverse (postorder (mirror l))) ++ preorder r
   ≡⟨ ap (λ t → x :: reverse (postorder (mirror l)) ++ t) (preorder-is-reverse-of-postorder-mirror r) ⟩
 x :: (reverse (postorder (mirror l))) ++ (reverse (postorder (mirror r)))
   ≡⟨ ap (λ t → t ++ reverse (postorder (mirror r))) (reverse-lemma x (postorder (mirror l))) ⟩
 reverse (postorder (mirror l) ++ [ x ]) ++ reverse (postorder (mirror r))
   ≡⟨ reverse-++-lemma' (postorder (mirror l) ++ [ x ]) (postorder (mirror r)) ⟩
 reverse (postorder (mirror r) ++ postorder (mirror l) ++ [ x ]) ∎
 

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
 insert'-preserves-all-smaller y x leaf y<x ⋆ = y<x , ⋆ , ⋆
 insert'-preserves-all-smaller y x (branch z l r) y<x (z<x , sl , sr) = γ (trichotomy z y)
   where
     γ : (trich : Trichotomy z y) → all-smaller (insert'-branch y z l r trich) x 
     γ (inl      z<y)  = z<x , sl , (insert'-preserves-all-smaller y x r y<x sr)
     γ (inr (inl z≡y)) = z<x , (sl , sr)
     γ (inr (inr z>y)) = z<x , (insert'-preserves-all-smaller y x l y<x sl , sr)

 insert'-preserves-all-bigger : (y x : X) (t : BT X)
                              → y > x
                              → all-bigger t x
                              → all-bigger (insert' y t) x
 insert'-preserves-all-bigger y x leaf y>x ⋆ = y>x , ⋆ , ⋆
 insert'-preserves-all-bigger y x (branch z l r) y>x (z>x , bl , br) = γ (trichotomy z y)
   where
     γ : (trich : Trichotomy z y) → all-bigger (insert'-branch y z l r trich) x
     γ (inl      z<y)  = z>x , bl , insert'-preserves-all-bigger y x r y>x br
     γ (inr (inl z≡y)) = z>x , (bl , br)
     γ (inr (inr z>y)) = z>x , insert'-preserves-all-bigger y x l y>x bl , br

 insert'-preserves-being-bst : (y : X) (t : BT X) → is-bst t → is-bst (insert' y t)
 insert'-preserves-being-bst y leaf ⋆ = ⋆ , ⋆ , ⋆ , ⋆
 insert'-preserves-being-bst y (branch x l r) (sl , br , il , ir) = γ (trichotomy x y)
   where
     γ : (trich : Trichotomy x y) → is-bst (insert'-branch y x l r trich)
     γ (inl      x<y)  = sl , (insert'-preserves-all-bigger y x r x<y br) , il , (insert'-preserves-being-bst y r ir)
     γ (inr (inl x≡y)) = sl , br , il , ir
     γ (inr (inr x>y)) = insert'-preserves-all-smaller y x l x>y sl , br , insert'-preserves-being-bst y l il , ir
```

## Exercise 2.2

**Prove** that `all-smaller` and `all-bigger` are decidable properties.

```agda
 all-smaller-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-smaller t x)
 all-smaller-is-decidable leaf x = inl ⋆
 all-smaller-is-decidable (branch y l r) x = ×-preserves-decidability
                                              (<-is-decidable y x) (×-preserves-decidability
                                                 (all-smaller-is-decidable l x) (all-smaller-is-decidable r x)) 
 

 all-bigger-is-decidable
  : (t : BT X) (x : X) → is-decidable (all-bigger t x)
 all-bigger-is-decidable leaf x = 𝟙-is-decidable
 all-bigger-is-decidable (branch y l r) x = ×-preserves-decidability
                                              (<-is-decidable x y) (×-preserves-decidability
                                                (all-bigger-is-decidable l x) (all-bigger-is-decidable r x))
```

Hence, prove that it is decidable whether or not a `BT X` is a BST.

```agda
 being-bst-is-decidable : (t : BT X) → is-decidable (is-bst t)
 being-bst-is-decidable leaf = 𝟙-is-decidable
 being-bst-is-decidable (branch x l r) = ×-preserves-decidability
                                           (all-smaller-is-decidable l x) (×-preserves-decidability
                                             (all-bigger-is-decidable r x) (×-preserves-decidability
                                               (being-bst-is-decidable l) (being-bst-is-decidable r)))
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
   γ (inl      y<x)  x∈ₛt = ap (λ t → branch y l t) (insert-same-tree-property x r ir x∈ₛt)
   γ (inr (inl y≡x)) x∈ₛt = refl _
   γ (inr (inr x<y)) x∈ₛt = ap (λ t → branch y t r) (insert-same-tree-property x l il x∈ₛt)
```

## Exercise 2.5

In the lecture, we prove that the efficient membership implies the
original membership on BSTs.

Now, **prove** the other direction of this.

```agda

 all-smaller-means-smaller : (y x : X) (l : BT X) → all-smaller l x → y ∈ l → y < x
 all-smaller-means-smaller y x (branch z l r) (z<x , sl , sr) (inl      y≡z)  = transport (_< x) (sym y≡z) z<x
 all-smaller-means-smaller y x (branch z l r) (z<x , sl , sr) (inr (inl y∈l)) = all-smaller-means-smaller y x l sl y∈l
 all-smaller-means-smaller y x (branch z l r) (z<x , sl , sr) (inr (inr y∈r)) = all-smaller-means-smaller y x r sr y∈r

 all-bigger-means-bigger : (y x : X) (r : BT X) → all-bigger r x → y ∈ r → y > x
 all-bigger-means-bigger y x (branch z r l) (z>x , br , bl) (inl      y≡z)  = transport (_> x) (sym y≡z) z>x
 all-bigger-means-bigger y x (branch z r l) (z>x , br , bl) (inr (inl y∈r)) = all-bigger-means-bigger y x r br y∈r
 all-bigger-means-bigger y x (branch z r l) (z>x , br , bl) (inr (inr y∈l)) = all-bigger-means-bigger y x l bl y∈l

 membership'-implies-membership : (y : X) (t : BT X) (i : is-bst t)
                                → y ∈ₛ' (t , i) → y ∈ₛ (t , i)
 membership'-implies-membership y (branch x l r) (sl , br , il , ir) y∈'t = γ (trichotomy x y) y∈'t
   where
     γ : (trich : Trichotomy x y) → y ∈ₛ' (branch x l r , sl , br , il , ir) → ∈ₛ-branch y x l r trich
     γ (inl      x<y)  (inl      y≡x)  = 𝟘-elim ((irreflexive' x y (sym y≡x)) x<y) 
     γ (inl      x<y)  (inr (inl y∈l)) = 𝟘-nondep-elim ((antisymmetric x y x<y) (all-smaller-means-smaller y x l sl y∈l)) 
     γ (inl      x<y)  (inr (inr y∈r)) = membership'-implies-membership y r ir y∈r
     γ (inr (inl x≡y)) (inl      y≡x)  = ⋆
     γ (inr (inl x≡y)) (inr (inl y∈l)) = ⋆
     γ (inr (inl x≡y)) (inr (inr y∈r)) = ⋆
     γ (inr (inr x>y)) (inl      y≡x)  = 𝟘-elim ((irreflexive' y x y≡x) x>y)
     γ (inr (inr x>y)) (inr (inl y∈l)) = membership'-implies-membership y l il y∈l
     γ (inr (inr x>y)) (inr (inr y∈r)) = 𝟘-nondep-elim (((antisymmetric x y) (all-bigger-means-bigger y x r br y∈r)) x>y)

 membership-implies-membership' : (y : X) (t : BT X) (i : is-bst t)
                                → y ∈ₛ (t , i) → y ∈ₛ' (t , i)
 membership-implies-membership' y (branch x l r) (sl , br , il , ir) y∈b = γ (trichotomy x y) y∈b
   where
     γ : (trich : Trichotomy x y) → ∈ₛ-branch y x l r trich → y ∈ₛ' (branch x l r , sl , br , il , ir) 
     γ (inl      x<y)  y∈r = inr (inr (membership-implies-membership' y r ir y∈r)) 
     γ (inr (inl x≡y)) ⋆   = inl (sym (x≡y))
     γ (inr (inr x>y)) y∈l = inr (inl (membership-implies-membership' y l il y∈l))
 
 being-in-is-decidable : (y : X) (t : BT X) → is-decidable (y ∈ₛ-bst t)
 being-in-is-decidable y leaf = 𝟘-is-decidable
 being-in-is-decidable y (branch x l r) = γ (trichotomy x y)
   where
     γ : (trich : Trichotomy x y)
       → ∈ₛ-branch y x l r trich
       ∔ (∈ₛ-branch y x l r trich → 𝟘)
     γ (inl      x<y)  = being-in-is-decidable y r
     γ (inr (inl x≡y)) = 𝟙-is-decidable
     γ (inr (inr x>y)) = being-in-is-decidable y l
```

## Exercise 2.6

**Prove** that if we insert an item into a binary search tree, the
size either remains the same or increases by one.

```agda
 insert-size-property : (x : X) (t : BT X) (i : is-bst t)
                      → (size (fst (insert x (t , i))) ≡ size t)
                      ∔ (size (fst (insert x (t , i))) ≡ size t + 1)
 insert-size-property x leaf i = inr (refl 1)
 insert-size-property x (branch y l r) (sl , br , il , ir) = γ (trichotomy y x)
   where
     γ : (trich : Trichotomy y x) → (size (insert'-branch x y l r trich) ≡ suc (size l + size r))
                                  ∔ (size (insert'-branch x y l r trich) ≡ suc ((size l + size r) + 1))
     γ (inl      y<x)  = ∔-elim _
                         (λ e → inl (ap (λ t → suc (size l + t)) e))
                         (λ e → inr (trans (ap (λ t → suc (size l + t)) e) (ap suc (sym (+-assoc (size l) (size r) 1)))))
                         (insert-size-property x r ir)
     γ (inr (inl y≡x)) = inl (ap suc (refl (size l + size r)))
     γ (inr (inr y>x)) = ∔-elim _
                         (λ e → inl (ap (λ t → (suc (t + size r))) e ))
                         (λ e → inr (trans (ap (λ t → suc (t + size r)) e)
                                           (ap suc (trans (+-assoc (size l) 1 (size r))
                                                          (trans (ap (λ z → size l + z) (sym (+-comm (size r) 1)))
                                                                 (sym (+-assoc (size l) (size r) 1)))))))
                         (insert-size-property x l il)
```

## Exercise 2.7

**Prove** that if an item is a member of a binary search tree that it
is inserted into.

*Hint:* You may need to prove some additional lemmas about
`∈ₛ-branch`.

```agda

 

 insert-membership-property : (x : X) (t : BT X) (i : is-bst t)  
                            → x ∈ₛ insert x (t , i)
 insert-membership-property x leaf ⋆ = γ (trichotomy x x)
   where
     γ : (trich : Trichotomy x x) → ∈ₛ-branch x x leaf leaf trich
     γ (inl      x<x)  = (irreflexive x) x<x
     γ (inr (inl x≡x)) = ⋆
     γ (inr (inr x>x)) = (irreflexive x) x>x
 insert-membership-property x (branch y l r) (sl , br , il , ir) = γ (trichotomy y x)
   where
     γ : (trich : Trichotomy y x) → x ∈ₛ-bst insert'-branch x y l r trich
     γ (inl      y<x ) = goal (trichotomy y x)
       where
         goal : (trich : Trichotomy y x) → ∈ₛ-branch x y l (insert' x r) trich
         goal (inl      y<x)  = insert-membership-property x r ir
         goal (inr (inl y≡x)) = ⋆
         goal (inr (inr y>x)) = 𝟘-nondep-elim ((antisymmetric x y y>x) y<x)
     γ (inr (inl y≡x)) = goal (trichotomy y x)
       where
         goal : (trich : Trichotomy y x) → ∈ₛ-branch x y l r trich
         goal (inl      y<x)  = 𝟘-nondep-elim ((irreflexive' y x y≡x) y<x)
         goal (inr (inl y≡x)) = ⋆
         goal (inr (inr y>x)) = 𝟘-nondep-elim (irreflexive' x y (sym y≡x) y>x)
     γ (inr (inr y>x)) = goal (trichotomy y x)
       where
         goal : (trich : Trichotomy y x) → ∈ₛ-branch x y (insert' x l) r trich
         goal (inl      y<x)  = 𝟘-nondep-elim ((antisymmetric x y y>x) y<x)
         goal (inr (inl y≡x)) = ⋆
         goal (inr (inr y>x)) = insert-membership-property x l il
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
 membership-insert-property x y leaf ⋆ y∈t = γ (trichotomy x y) y∈t
   where
     γ : (trich : Trichotomy x y)
       → ∈ₛ-branch y x leaf leaf trich
       → (y ≡ x) ∔ 𝟘
     γ (inr (inl x≡y)) y∈b = inl (sym x≡y)
 membership-insert-property x y (branch z l r) (sl , sr , il , ir) y∈b = γ (trichotomy z y) (trichotomy z x) y∈b
   where
     γ : (trich-zy : Trichotomy z y)
       → (trich-zx : Trichotomy z x)
       → y ∈ₛ-bst insert'-branch x z l r trich-zx
       → (y ≡ x) ∔ ∈ₛ-branch y z l r trich-zy
     γ (inl      z<y)  (inl      z<x)  y∈t = goal (trichotomy z y) y∈t
       where
         goal : (trich : Trichotomy z y) → ∈ₛ-branch y z l (insert' x r) trich → (y ≡ x) ∔ (y ∈ₛ-bst r)
         goal (inl      z<y)  y∈r = membership-insert-property x y r ir y∈r
         goal (inr (inl z≡y)) ⋆   = 𝟘-nondep-elim ((irreflexive' z y z≡y) z<y)
         goal (inr (inr z>y)) y∈l = 𝟘-nondep-elim ((antisymmetric y z z>y) z<y)
     γ (inl      z<y)  (inr (inl z≡x)) y∈t = goal (trichotomy z y) y∈t
       where
         goal : (trich : Trichotomy z y) → ∈ₛ-branch y z l r trich → (y ≡ x) ∔ (y ∈ₛ-bst r)
         goal (inl      z<y)  y∈r = inr y∈r
         goal (inr (inl z≡y)) ⋆   = 𝟘-nondep-elim ((irreflexive' z y z≡y) z<y)
         goal (inr (inr z>y)) y∈l = 𝟘-nondep-elim ((antisymmetric z y z<y) z>y)
     γ (inl      z<y)  (inr (inr z>x)) y∈t = goal (trichotomy z y) y∈t
       where
         goal : (trich : Trichotomy z y) → ∈ₛ-branch y z (insert' x l) r trich → (y ≡ x) ∔ (y ∈ₛ-bst r)
         goal (inl      z<y)  y∈r = inr y∈r
         goal (inr (inl z≡y)) ⋆   = 𝟘-nondep-elim ((irreflexive' z y z≡y) z<y)
         goal (inr (inr z>y)) y∈l = 𝟘-nondep-elim ((antisymmetric z y z<y) z>y)
     γ (inr (inl z≡y)) (inl      z<x)  y∈t = inr ⋆
     γ (inr (inr z>y)) (inl      z<x)  y∈t = goal (trichotomy z y) y∈t
       where
         goal : (trich : Trichotomy z y) → ∈ₛ-branch y z l (insert' x r) trich → (y ≡ x) ∔ (y ∈ₛ-bst l)
         goal (inl      z<y)  y∈r = 𝟘-nondep-elim ((antisymmetric z y z<y) z>y)
         goal (inr (inl z≡y)) ⋆   = 𝟘-nondep-elim ((irreflexive' y z (sym z≡y)) z>y)
         goal (inr (inr z>y)) y∈l = inr y∈l
     γ (inr (inl z≡y)) (inr (inl z≡x)) y∈t = inr ⋆
     γ (inr (inl z≡y)) (inr (inr z>x)) y∈t = inr ⋆
     γ (inr (inr z>y)) (inr (inl z≡x)) y∈t = goal (trichotomy z y) y∈t
       where
         goal : (trich : Trichotomy z y) → ∈ₛ-branch y z l r trich → (y ≡ x) ∔ (y ∈ₛ-bst l)
         goal (inl      z<y)  y∈r = 𝟘-nondep-elim ((antisymmetric z y z<y) z>y)
         goal (inr (inl z≡y)) ⋆   = 𝟘-nondep-elim ((irreflexive' y z (sym z≡y)) z>y)
         goal (inr (inr z>y)) y∈l = inr y∈l
     γ (inr (inr z>y)) (inr (inr z>x)) y∈t = goal (trichotomy z y) y∈t
       where
         goal : (trich : Trichotomy z y) → ∈ₛ-branch y z (insert' x l) r trich → (y ≡ x) ∔ (y ∈ₛ-bst l)
         goal (inl      z<y)  y∈r = 𝟘-nondep-elim ((antisymmetric z y z<y) z>y)
         goal (inr (inl z≡y)) ⋆   = 𝟘-nondep-elim ((irreflexive' y z (sym z≡y)) z>y)
         goal (inr (inr z>y)) y∈l = membership-insert-property x y l il y∈l
```

# Bonus Exercise (Very, very hard.)

**Prove** that flattening a BST results in a sorted list.

```agda
 flattened-BST-is-sorted : (t : BT X) → is-bst t → Sorted S (flatten t)
 flattened-BST-is-sorted leaf ⋆ = nil-sorted
 flattened-BST-is-sorted (branch x l r) (sl , br , il , ir)
   = {!γ l r x (flattened-BST-is-sorted r ir) (flattened-BST-is-sorted l il)!}
   where
     γ : (l r : BT X) (x : X) → Sorted S (flatten l) → Sorted S (flatten r) → Sorted S (flatten l ++ (x :: flatten r)) 
     γ leaf r x sortl sortr = {!!}
     γ (branch x₁ l l₁) r x sortl sortr = {!!}
```
