```agda
{-# OPTIONS --without-K --safe #-}

module BST where

open import prelude
open import strict-total-order
open import decidability
open import natural-numbers-functions
open import List-functions
```

In this file, we will first define the type of *binary trees* (BTs),
as well as define some operations on this type and prove some
properties about them.

Then, we will define binary *search* trees in three ways. The first
approach defines BSTs as BTs that satisfy certain conditions. The
second and third approaches define BSTs from the ground up as a type
that *only* permits the construction of BSTs. The second and third
approaches differ in that the third approach is more efficient.

# Binary Trees

First, we define the type of BTs. A BT over type A is either:
 * a leaf containing no data,
 * a branch containing some data that has a left and right subtree.

```agda
data BT (A : Type) : Type where
 leaf   : BT A
 branch : A → BT A → BT A → BT A
```

For example,

```code
branch 5
  (branch 8
    leaf
    (branch 9
      (branch 1
        (branch 2
          leaf
          leaf)
        leaf)
      leaf))
  (branch 2 leaf leaf)
```

constructs the tree visualised below:

```code
       5
      / \
     /   \
    8     2
     \   
      \  
       9
      /
     /
    1
   /
  /
 2
```

## Size

The size of a BT is how many items of data it contains.

```agda
size : {A : Type} → BT A → ℕ
size leaf         = 0
size (branch x l r) = 1 + size l + size r
```

Emptiness and nonemptiness can be defined using size.

```agda
empty' nonempty' : {A : Type} → BT A → Type
empty'    t = size t ≡ 0
nonempty' t = ¬ (empty' t)
```

## Membership

We define the type `x ∈ t` which is inhabited if `x : A` is a member of
the tree `t : BT A`.

```agda
_∈_ : {A : Type} → A → BT A → Type
x ∈ leaf = 𝟘
x ∈ branch y l r = (x ≡ y) ∔ (x ∈ l) ∔ (x ∈ r)
```

Emptiness and nonemptiness can also be defined using membership.

```agda
nonempty empty : {A : Type} → BT A → Type
nonempty {A} t = Σ x ꞉ A , x ∈ t 
empty        t = ¬ (nonempty t)
```

We prove that both definitions of emptiness and nonemptiness are the
same.

```agda
empty-is-empty' : {A : Type} (t : BT A) → empty t ⇔ empty' t
empty-is-empty' {A} leaf = ltr , rtl
 where
  ltr : empty leaf → empty' {A} leaf
  ltr _ = refl 0
  rtl : empty' {A} leaf → empty leaf
  rtl _ (x , ())
empty-is-empty' {A} (branch x l r) = ltr , rtl
 where
  ltr : empty (branch x l r) → empty' (branch x l r)
  ltr f = 𝟘-elim (f (x , inl (refl x))) 
  rtl : empty' (branch x l r) → empty (branch x l r)
  rtl ()

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

## Mirroring

Trees can be mirrored.

```agda
mirror : {A : Type} → BT A → BT A
mirror leaf = leaf
mirror (branch x l r) = branch x (mirror r) (mirror l)
```

Mirroring the same tree twice gives back the original tree. Let's
prove that!

```agda
mirror-is-involutive : {A : Type} → mirror ∘ mirror ∼ id {BT A}
mirror-is-involutive leaf = refl leaf
mirror-is-involutive (branch x l r)
 = mirror (mirror (branch x l r))
     ≡⟨ refl _ ⟩
   branch x (mirror (mirror l)) (mirror (mirror r))
     ≡⟨ ap (λ - → branch x - (mirror (mirror r)))
           (mirror-is-involutive l) ⟩
   branch x l (mirror (mirror r))
     ≡⟨ ap (branch x l) (mirror-is-involutive r) ⟩
   branch x l r ∎
```

## Flattening

By performing an in-order traversal of a binary tree, we can 'flatten'
it to a list.

```agda
flatten : {A : Type} → BT A → List A
flatten leaf = []
flatten (branch x l r) = flatten l ++ [ x ] ++ flatten r
```

Furthermore, we can prove that flattening a mirrored tree is the same
as reversing a flattened tree.

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

# Binary Search Trees - First Approach

A binary search tree is a binary tree such that, at every branch:
 * the left subtrees values are smaller than the branch's value,
 * the right subtrees values are bigger than the branch's value.

Therefore, we require a strict total order on the type of the tree's
values.

```agda
module first-approach (X : Type) (s : StrictTotalOrder X) where

 open StrictTotalOrder s
```

## Definition

We now define the predicates `all-smaller` and `all-bigger`, which in
turn allow us to define `is-bst`.

```agda
 all-smaller  : BT X → X → Type
 all-smaller leaf           y = 𝟙
 all-smaller (branch x l r) y = (x < y)
                              × all-smaller l y
                              × all-smaller r y

 all-bigger  : BT X → X → Type
 all-bigger leaf           y = 𝟙
 all-bigger (branch x l r) y = (x > y)
                             × all-bigger l y
                             × all-bigger r y

 is-bst : BT X → Type
 is-bst leaf           = 𝟙
 is-bst (branch x l r) = all-smaller l x
                       × all-bigger r x
                       × is-bst l
                       × is-bst r
```

The type of binary search trees are those binary trees that satisfy
`is-bst`.

```agda
 BST : Type
 BST = Σ t ꞉ BT X , is-bst t
```

## Efficient membership

We can define the `_∈_` relation on BSTs by simply using the one on
BTs.

```agda
 _∈ₛ'_ : X → BST → Type
 x ∈ₛ' (t , _) = x ∈ t
```

However, this is clearly inefficient --- consider checking whether `5`
is in the below BST:

```code
       4
      / \
     /   \
    2     5
   / \   
  /   \  
 1     3
```

Once we see that `4` is the value of the first branch, we can use a
binary search method to only consider the right tree, without ever
checking the left.

To implement this, we will need to use proofs of trichotomy.

```agda
 Trichotomy : X → X → Type
 Trichotomy x y = (x < y) ∔ (x ≡ y) ∔ (x > y)
```

The base case is easy, clearly nothing is in an empty tree.
For the inductive case, we compare whether the branch value `x` is 
is smaller than, equal to, or larger than the searched-for value `y`:
 * If `x < y` then we search only the right subtree,
 * If `x ≡ y` then `y` is in the tree,
 * if `x > y` then we search only the left subtree.

```agda
 _∈ₛ-bst_ : X → BT X → Type

 ∈ₛ-branch : (y x : X) (l r : BT X) → Trichotomy x y → Type
 ∈ₛ-branch y x l r (inl      x<y)  = y ∈ₛ-bst r
 ∈ₛ-branch y x l r (inr (inl x≡y)) = 𝟙
 ∈ₛ-branch y x l r (inr (inr x>y)) = y ∈ₛ-bst l

 y ∈ₛ-bst leaf   = 𝟘
 y ∈ₛ-bst (branch x l r) = ∈ₛ-branch y x l r (trichotomy x y)

 _∈ₛ_ : X → BST → Type
 x ∈ₛ (t , _) = x ∈ₛ-bst t
```

Let's prove that the more efficient version implies the original
version.

```agda
 membership-implies-membership' : (y : X) (t : BT X) (i : is-bst t)
                                → y ∈ₛ (t , i) → y ∈ₛ' (t , i)
 membership-implies-membership' y leaf _ = id
 membership-implies-membership' y (branch x l r) (s , b , il , ir)
  = γ (trichotomy x y)
  where
   γ : (trich : Trichotomy x y)
     → ∈ₛ-branch y x l r trich
     → y ∈ (branch x l r)
   γ (inl      x<y ) y∈r
    = inr (inr (membership-implies-membership' y r ir y∈r))
   γ (inr (inl x≡y)) ⋆
    = inl (sym x≡y)
   γ (inr (inr x>y)) y∈l
    = inr (inl (membership-implies-membership' y l il y∈l))
```

Aditionally, we can prove that being a member of a BST is decidable.

```agda
 being-in-is-decidable : (y : X) (t : BT X) → is-decidable (y ∈ₛ-bst t)
 being-in-is-decidable y leaf = 𝟘-is-decidable
 being-in-is-decidable y (branch x l r) with trichotomy x y
 ... | inl x<y       = being-in-is-decidable y r
 ... | inr (inl y≡x) = 𝟙-is-decidable
 ... | inr (inr x>y) = being-in-is-decidable y l
```

## Insert

The insert function is also defined using proofs of trichotomy.

```agda
 insert : X → BST → BST
```

In order to define `insert`, we will:
 1. First define what it does on the underlying BT,
 2. Prove that it preserves `is-smaller` and `is-bigger`, and therefore
    that it preserves `is-bst`.
 3. Use the above constructions to define `insert`.

So let's first define what `insert` does on the underlying BT.

```agda
 insert' : X → BT X → BT X

 insert'-branch
  : (y x : X) (l r : BT X) → Trichotomy x y → BT X
 insert'-branch y x l r (inl      x<y)  = branch x l (insert' y r)
 insert'-branch y x l r (inr (inl x≡y)) = branch x l r
 insert'-branch y x l r (inr (inr x>y)) = branch x (insert' y l) r

 insert' y leaf           = branch y leaf leaf  
 insert' y (branch x l r) = insert'-branch y x l r (trichotomy x y)
```

Second, we prove that `insert'` preserves `is-smaller` and `is-bigger`
and, thus, `is-bst`.

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

 insert'-preserves-being-bst
  : (y : X) (t : BT X) → is-bst t → is-bst (insert' y t)
 insert'-preserves-being-bst y leaf   ⋆ = ⋆ , ⋆ , ⋆ , ⋆
 insert'-preserves-being-bst y (branch x l r) (s , b , il , ir)
  = γ (trichotomy x y)
  where
   γ : (trich : Trichotomy x y)
     → is-bst (insert'-branch y x l r trich)
   γ (inl x<y) = s , insert'-preserves-all-bigger y x r x<y b
               , il , insert'-preserves-being-bst y r ir
   γ (inr (inl x≡y)) = s , b , il , ir
   γ (inr (inr y<x)) = insert'-preserves-all-smaller y x l y<x s , b
                     , insert'-preserves-being-bst y l il , ir
```

We can now define `insert` on the type of BSTs.

```agda
 insert x (t , i) = insert' x t , insert'-preserves-being-bst x t i
```

Additionally, we can prove that being a BST is decidable.

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


 being-bst-is-decidable : (t : BT X) → is-decidable (is-bst t)
 being-bst-is-decidable leaf   = 𝟙-is-decidable
 being-bst-is-decidable (branch x l r) =
   ×-preserves-decidability (all-smaller-is-decidable l x)
  (×-preserves-decidability (all-bigger-is-decidable r x)
  (×-preserves-decidability (being-bst-is-decidable l)
                            (being-bst-is-decidable r)))
```

## More properties about insert

We have defined insert. Now we will prove various properties about it,
using proofs of trichotomy.

```agda
 insert'-property₀ : (x : X) (t : BT X) (i : is-bst t)
                   → x ∈ₛ (t , i)
                   → fst (insert x (t , i)) ≡ t
 insert'-property₀ x (branch y l r) (s , b , il , ir)
  = γ (trichotomy y x)
  where
   γ : (trich : Trichotomy y x)
     → ∈ₛ-branch x y l r trich
     → insert'-branch x y l r trich ≡ branch y l r
   γ (inl y<x) x∈ₛt = ap (branch y l) (insert'-property₀ x r ir x∈ₛt)
   γ (inr (inl y≡x)) x∈ₛt = refl (branch y l r)
   γ (inr (inr x<y)) x∈ₛt
    = ap (λ - → branch y - r) (insert'-property₀ x l il x∈ₛt)

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
               
 insert'-property₁ : (x : X) (t : BT X) (i : is-bst t)  
                   → x ∈ₛ insert x (t , i)
 insert'-property₁ x leaf i = γ (trichotomy x x)
  where
   γ : (trich : Trichotomy x x) → ∈ₛ-branch x x leaf leaf trich
   γ (inl x<x) = irreflexive x x<x
   γ (inr (inl x≡x)) = ⋆
   γ (inr (inr x<x)) = irreflexive x x<x
 insert'-property₁ x (branch y l r) (s , b , il , ir)
  = γ (trichotomy y x)
  where
   γ : (trich : Trichotomy y x)
     → x ∈ₛ-bst insert'-branch x y l r trich
   γ (inl y<x)
    = ∈ₛ-branch-right x y l (insert' x r) (trichotomy y x)
        y<x (insert'-property₁ x r ir)
   γ (inr (inl y≡x))
    = ∈ₛ-branch-middle x y l r (trichotomy y x) y≡x
   γ (inr (inr y>x))
    = ∈ₛ-branch-left x y (insert' x l) r (trichotomy y x)
        y>x (insert'-property₁ x l il)

 insert'-property₂ : (x y : X) (t : BT X) (i : is-bst t)
                   → y ∈ₛ insert x (t , i)
                   → (y ≡ x) ∔ (y ∈ₛ (t , i))
 insert'-property₂ x y leaf i y∈ₛt
  = γ (trichotomy x y) y∈ₛt
  where
   γ : (trich : (x < y) ∔ (x ≡ y) ∔ (x > y))
     → ∈ₛ-branch y x leaf leaf trich
     → (y ≡ x) ∔ 𝟘
   γ (inl x<y) ()
   γ (inr (inl x≡y)) ⋆ = inl (sym x≡y)
   γ (inr (inr x>y)) ()
 insert'-property₂ x y (branch z l r) (s , b , il , ir)
  = γ (trichotomy z x) (trichotomy z y)
  where
   γ : (trich-zx : (z < x) ∔ (z ≡ x) ∔ (z > x))
     → (trich-zy : (z < y) ∔ (z ≡ y) ∔ (z > y))
     → y ∈ₛ-bst insert'-branch x z l r trich-zx
     → (y ≡ x) ∔ ∈ₛ-branch y z l r trich-zy
   γ (inl z<x) (inl z<y) y∈ₛt
    = insert'-property₂ x y r ir
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
    = insert'-property₂ x y l il
        (∈ₛ-branch-left' y z (insert' x l) r (trichotomy z y) z>y y∈ₛt)
   γ (inl z<x) (inr (inl (refl _))) y∈ₛt = inr ⋆
   γ (inr (inl (refl _))) (inr (inl (refl _))) y∈ₛt = inr ⋆
   γ (inr (inr z>x)) (inr (inl (refl _))) y∈ₛt = inr ⋆

 insert'-property₃ : (x : X) (t : BT X) (i : is-bst t)
                  → (size (fst (insert x (t , i))) ≡ size t)
                  ∔ (size (fst (insert x (t , i))) ≡ size t + 1)
 insert'-property₃ x leaf   i = inr (refl 1)
 insert'-property₃ x (branch y l r) (s , b , il , ir)
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
                    (insert'-property₃ x r ir)
   γ (inr (inl y≡x)) = inl (refl _)
   γ (inr (inr y>x))
    = ∔-nondep-elim (λ e → inl (ap (λ - → suc (- + size r)) e))
                    (λ e → inr (ap suc
                      (trans (ap (_+ size r) e)
                        (trans (ap (_+ size r) (+-comm (size l) 1))
                          (+-comm 1 (size l + size r))))))
                    (insert'-property₃ x l il)
```

# Binary Search Trees - Second Approach

For our second approach to BSTs, we define a type `BST` not as a
'subtype' of `BT X` but from the ground up.

By doing this, we define a type that only permits the construction of
binary search trees --- i.e., we no longer use a predicate `is-bst`.

```agda
module second-approach (X : Type) (s : StrictTotalOrder X) where

 open StrictTotalOrder s
 open first-approach X s using (Trichotomy)
```

## Definition

We will reuse much of the code of the first approach, but this time we
must define the type `BST` *at the same time* as we define what the
predicates `all-smaller` and `all-bigger`.

```agda
 data BST : Type
 all-smaller : BST → X → Type
 all-bigger  : BST → X → Type
```

This is because the `branch` constructor of `BST` must take in proofs
that:
 * the left subtrees values are smaller than the branch's value,
 * the right subtrees values are bigger than the branch's value.

Rather than these proofs being required at a later stage, they are
used at the point we construct the binary search tree. This is called
*mutual recursion*.

```agda
 data BST where
  leaf : BST
  branch : (x : X) (l r : BST)
           (G : all-smaller l x) (S : all-bigger r x) → BST

 all-smaller leaf           y = 𝟙
 all-smaller (branch x l r G S) y = (x < y)
                                  × all-smaller l y
                                  × all-smaller r y
                                  
 all-bigger leaf               y = 𝟙
 all-bigger (branch x l r G S) y = (x > y)
                                 × all-bigger l y
                                 × all-bigger r y
```

## Insert

To define `insert`, the following four functions (from the first
approach) must be defined mutually recursively.

```agda                                 
 insert : X → BST → BST
 
 insert-branch
  : (y x : X) (l r : BST)
    (G : all-smaller l x) (S : all-bigger r x) → Trichotomy x y → BST

 insert-preserves-all-smaller : (y x : X) (t : BST)
                               → y < x
                               → all-smaller t x
                               → all-smaller (insert y t) x

 insert-preserves-all-bigger : (y x : X) (t : BST)
                             → y > x
                             → all-bigger t x
                             → all-bigger (insert y t) x
```

The order that we define these functions often matters as to whether
Agda can solve the constraints of the problems we're dealing with.

Try to re-order the following definitions and see what happens.

```agda
 insert y leaf = branch y leaf leaf ⋆ ⋆ 
 insert y (branch x l r G S)
  = insert-branch y x l r G S (trichotomy x y)
 
 insert-branch y x l r S B (inl      x<y)
  = branch x l (insert y r) S (insert-preserves-all-bigger y x r x<y B) 
 insert-branch y x l r S B (inr (inl x≡y))
  = branch x l r S B
 insert-branch y x l r S B (inr (inr x>y))
  = branch x (insert y l) r (insert-preserves-all-smaller y x l x>y S) B

 insert-preserves-all-smaller y x leaf y<x b = y<x , ⋆ , ⋆
 insert-preserves-all-smaller y x (branch z l r S B) y<x (x<z , sl , sr)
  = γ (trichotomy z y)
  where
   γ : (trich : Trichotomy z y)
     → all-smaller (insert-branch y z l r S B trich) x
   γ (inl      z<y )
    = x<z , sl , insert-preserves-all-smaller y x r y<x sr 
   γ (inr (inl (refl _))) = x<z , sl , sr
   γ (inr (inr z>y))
    = x<z , insert-preserves-all-smaller y x l y<x sl , sr 
    
 insert-preserves-all-bigger y x leaf   y>x b = y>x , ⋆ , ⋆
 insert-preserves-all-bigger y x (branch z l r G S) y>x (x<z , bl , br)
  = γ (trichotomy z y)
  where
   γ : (trich : Trichotomy z y)
     → all-bigger (insert-branch y z l r G S trich) x
   γ (inl      z<y )
    = x<z , bl , insert-preserves-all-bigger y x r y>x br
   γ (inr (inl (refl _))) = x<z , bl , br
   γ (inr (inr z>y))
    = x<z , insert-preserves-all-bigger y x l y>x bl , br 
```

# Binary Search Trees - Third Approach (Advanced)

Our third approach follows our second approach in that we define a
type `BST` that can only construct binary search trees.

```agda
module third-approach (X : Type) (s : StrictTotalOrder X) where

 open StrictTotalOrder s
 open first-approach X s using (Trichotomy)
```

## Definition

In fact, the initial code and indeed the definition of `BST` is exactly
the same as in the second approach.

```agda
 data BST : Type
 all-smaller : BST → X → Type
 all-bigger  : BST → X → Type

 data BST where
  leaf : BST
  branch : (x : X) (l r : BST)
           (G : all-smaller l x) (S : all-bigger r x) → BST
```

The difference comes with our definition of `all-smaller` and
`all-bigger`.

For `all-smaller`, in the branch case, rather than checking that
*every* element of both subtrees is smaller than `y`, we can compare
`y` *only with* the largest value currently in the tree.

This will be the rightmost value of the tree.

```agda
 all-smaller leaf y                                  = 𝟙
 all-smaller (branch x l leaf G S) y                 = y > x
 all-smaller (branch x l r@(branch _ _ _ _ _) G S) y = all-smaller r y
```

In the above, we use `r@` to pattern match on `r` while still allowing
us to use `r` to refer to the whole pattern.

We follow the same approach for `all-bigger`:

```agda
 all-bigger  leaf y                                  = 𝟙
 all-bigger  (branch x leaf r G S) y                 = y < x
 all-bigger  (branch x l@(branch _ _ _ _ _) r G S) y = all-bigger l y
```

# Insert

TODO. Change `_≺_` and `_≻_` to `all-smaller` and `all-bigger` and add
comments.

```agda
 _≺_ : X → BST → Type
 _≻_ : X → BST → Type

 x ≺ t = all-bigger  t x
 x ≻ t = all-smaller t x

 ≺leaf   : (y : X) → y ≺ leaf  
 ≺leaf   y = ⋆

 ≺-trans : (x z : X) (t : BST) → x < z → z ≺ t → x ≺ t
 ≺-trans x z leaf   _ _ = ⋆
 ≺-trans x z (branch w leaf   r G S) = transitive
 ≺-trans x z (branch w l@(branch _ _ _ _ _) r G S) = ≺-trans x z l
 
 ≻leaf    : (y : X) → y ≻ leaf  
 ≻leaf   y = ⋆

 ≺branch₀ : (x z : X) (l r : BST) (z≻l : z ≻ l) (z≺r : z ≺ r)
          → x ≺ branch z l r z≻l z≺r
          → x < z

 ≻branch₀ : (x z : X) (l r : BST) (z≻l : z ≻ l) (z≺r : z ≺ r)
          → x ≻ branch z l r z≻l z≺r
          → x > z

 ≺branch₀ x z leaf r x≻l z≺r x≺b = x≺b
 ≺branch₀ x z (branch w l' r' G S) r x≻l z≺r x≺b
  = transitive (≺branch₀ x w l' r' G S x≺b) (≻branch₀ z w l' r' G S x≻l)
        
 ≻branch₀ x z l leaf   z≻l z≺r x>z = x>z
 ≻branch₀ x z l (branch w l' r' G S) z≻l z≺r x≻b
  = transitive (≺branch₀ z w l' r' G S z≺r) (≻branch₀ x w l' r' G S x≻b)

 ≺branch₁ : (x z : X) (l r : BST) (z≻l : z ≻ l) (z≺r : z ≺ r)
          → x ≺ l
          → x < z
          → x ≺ branch z l r z≻l z≺r
 ≺branch₁ x z leaf r z≻l z≺r x≺l x<z = x<z
 ≺branch₁ x z (branch _ _ _ _ _) r z≻l z≺r x≺l x<z = x≺l

 ≻branch₁ : (x z : X) (l r : BST) (z≻l : z ≻ l) (z≺r : z ≺ r)
        → x ≻ r
        → x > z
        → x ≻ branch z l r z≻l z≺r
 ≻branch₁ x z l leaf   z≻l z≺r x≻r x>z = x>z
 ≻branch₁ x z l (branch _ _ _ _ _) z≻l z≺r x≻r x>z = x≻r

 ≻-trans : (x z : X) (t : BST) → x > z → z ≻ t → x ≻ t
 ≻-trans x z leaf   _ _ = ⋆
 ≻-trans x z (branch w l leaf   G S) x>z z≻t = transitive z≻t x>z
 ≻-trans x z (branch w l r@(branch _ _ _ _ _) G S) = ≻-trans x z r
 
 _∈ₛ_ : X → BST → Type
 _∈ₛ_ y leaf   = 𝟘
 _∈ₛ_ y (branch x l r G S) with trichotomy y x
 _∈ₛ_ y (branch x l r G S) | inl x<y = y ∈ₛ l
 _∈ₛ_ y (branch x l r G S) | inr (inl y≡x) = 𝟙
 _∈ₛ_ y (branch x l r G S) | inr (inr y<x) = y ∈ₛ r

 insert'' : X → BST → BST
 insert''-≺ : (x y : X) (r : BST) → x < y → x ≺ r → x ≺ insert'' y r
 insert''-≻ : (x y : X) (l : BST) → x > y → x ≻ l → x ≻ insert'' y l

 insert'' y leaf  
  = branch y leaf   leaf   (≺leaf   y) (≻leaf   y)
 insert'' y (branch x l r x≻l x≺r) with trichotomy x y
 insert'' y (branch x l r x≻l x≺r) | inl x<y
  = branch x l (insert'' y r) x≻l (insert''-≺ x y r x<y x≺r)
 insert'' y (branch x l r x≻l x≺r) | inr (inl x≡y)
  = branch x l r x≻l x≺r
 insert'' y (branch x l r x≻l x≺r) | inr (inr x>y)
  = branch x (insert'' y l) r (insert''-≻ x y l x>y x≻l) x≺r

 insert''-≺ x y leaf   x<y x≺t
  = x<y
 insert''-≺ x y (branch z _ _ _ _) _ _ with trichotomy z y
 insert''-≺ x y (branch z leaf   _ _ _) x<y x≺t
  | inl z<y = x≺t
 insert''-≺ x y (branch z (branch _ _ _ _ _) _ z≻l z≺r) x<y x≺t
  | inl z<y = x≺t    
 insert''-≺ x y (branch z _ _ _ _) x<y x≺t
  | inr (inl z≡y) = x≺t 
 insert''-≺ x y (branch z leaf   _ _ _) x<y x≺t
  | inr (inr z>y) = x<y
 insert''-≺ x y (branch z l@(branch _ _ _ _ _) r z≻l z≺r) x<y x≺t
  | inr (inr z>y)
  = ≺branch₁ x z (insert'' y l) r
      (insert''-≻ z y l z>y z≻l)
      z≺r
      (insert''-≺ x y l x<y x≺t)
      (transitive x<y z>y)
 insert''-≻ x y leaf   x>y x≻t
  = x>y
 insert''-≻ x y (branch z _ _ _ _) _ _ with trichotomy z y
 insert''-≻ x y (branch z _ leaf   _ _) x>y x≻t
  | inl z<y = x>y
 insert''-≻ x y (branch z l r@(branch _ _ _ _ _) z≻l z≺r) x>y x≻t
  | inl z<y
  = ≻branch₁ x z l (insert'' y r) z≻l
      (insert''-≺ z y r z<y z≺r)
      (insert''-≻ x y r x>y x≻t)
      (transitive z<y x>y)
 insert''-≻ x y (branch z _ _ _ _) x>y x≻t
  | inr (inl z≡y) = x≻t
 insert''-≻ x y (branch z _ leaf   _ _) x>y x≻t
  | inr (inr z>y) = x≻t
 insert''-≻ x y (branch z _ (branch _ _ _ _ _) _ _) x>y x≻t
  | inr (inr z>y) = x≻t
```

TODO.

Claim: the types BST and BST are isomorphic.

 ϕ : BST → BST
 ϕ leaf   = leaf   , ⋆
 ϕ (branch x l r x≻l x≺r) with ϕ l with ϕ r
 ϕ (branch x l r x≻l x≺r) | (l' , l'-is-bst) | (r' , r'-is-bst)
  = branch x l' r' , {!!}

 γ : BST → BST
 γ (leaf   , _) = leaf  
 γ (branch x l r , (smaller , bigger , l-is-bst , r-is-bst)) = {!!}
