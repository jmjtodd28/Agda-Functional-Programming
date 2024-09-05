```agda
{-# OPTIONS --without-K --safe #-}

module BST-rewrite where

  open import prelude
  open import strict-total-order
  open import decidability
  open import natural-numbers-functions
  open import List-functions

  data BT (A : Type) : Type where
    leaf   : BT A
    branch : A → BT A → BT A → BT A

  size : {A : Type} → BT A → ℕ
  size leaf = 0
  size (branch x l r) = suc (size l + size r)

  empty' nonempty' : {A : Type} → BT A → Type
  empty'    t = size t ≡ 0
  nonempty' t = ¬ (empty' t)

  _∈_ : {A : Type} → A → BT A → Type
  x ∈ leaf = 𝟘
  x ∈ branch y l r = (x ≡ y) ∔ (x ∈ l) ∔ (x ∈ r)

  -- Non empty and empty can be defined using membership

  nonempty empty : {A : Type} → BT A → Type
  nonempty {A} t = Σ x ꞉ A , x ∈ t 
  empty        t = ¬ (nonempty t)

  empty-is-empty' : {A : Type} (t : BT A) → empty t ⇔ empty' t
  empty-is-empty' {A} leaf =  ltr , rtl
    where
     ltr : empty leaf → empty' {A} leaf
     ltr x = refl 0
     rtl : empty' {A} leaf → empty leaf
     rtl (refl _) (x , x∈leaf) = x∈leaf -- the second varialbe is (x , x∈leaf) because if we look at empty, it means it s not nonemtpy and nonemtpy is a proof of given an x , x is in the leaf
  empty-is-empty' (branch x l r) = ltr , rtl
    where
      ltr : empty (branch x l r) → empty' (branch x l r)
      ltr f = 𝟘-elim (f (x , inl (refl x)))
        --nonempty (branch x l r)
        -- Σ y ꞉ A , y ∈ t
        -- Σ y ꞉ A , (y ≡ x) ∔ (y ∈ l) ∔ (y ∈ r)
      rtl : empty' (branch x l r) → empty (branch x l r)
      rtl () (a , b)

  nonempty-is-nonempty' : {A : Type} (t : BT A)
                        → nonempty t ⇔ nonempty' t
  nonempty-is-nonempty' {A} leaf = ltr , rtl
    where
      ltr : nonempty leaf → nonempty' {A} leaf
      ltr (a , p) (refl .0) = p
      -- nonempty leaf
      -- Σ x ꞉ A , x ∈ t
      -- Σ x ꞉ A , 𝟘 it is zero since x ∈ leaf = 𝟘 hence why the p is 𝟘
      rtl : nonempty' {A} leaf → nonempty leaf
      rtl f = 𝟘-elim (f (refl (zero))) 
      --nonempty' leaf
      --size leaf ≡ 0 → 𝟘
      -- 0 ≡ 0 → 𝟘
  nonempty-is-nonempty' {A} (branch x l r) = ltr , rtl
    where
      ltr : nonempty (branch x l r) → nonempty' (branch x l r)
      ltr f ()
      rtl : nonempty' (branch x l r) → nonempty (branch x l r)
      rtl f = x , inl (refl x)

  mirror : {A : Type} → BT A → BT A
  mirror leaf = leaf
  mirror (branch x l r) = branch x (mirror r) (mirror l)

  mirror-is-involutive : {A : Type} → mirror ∘ mirror ∼ id {BT A}
  mirror-is-involutive leaf = refl leaf
  mirror-is-involutive (branch x l r) =
   branch x (mirror (mirror l)) (mirror (mirror r)) ≡⟨ ap (λ z → branch x (mirror (mirror l)) z ) r-IH ⟩
   branch x (mirror (mirror l)) r                   ≡⟨ ap (λ z → branch x z r) l-IH   ⟩
   branch x l r ∎
    where
      l-IH : mirror (mirror l) ≡ l
      l-IH = mirror-is-involutive l
      r-IH : mirror (mirror r) ≡ r
      r-IH = mirror-is-involutive r

  flatten : {A : Type} → BT A → List A
  flatten leaf = []
  flatten (branch x l r) = flatten l ++ [ x ] ++ flatten r

  reverse-++-lemma : {A : Type} (r : List A) (x : A) (l : List A)
                 → reverse r ++ [ x ] ++ reverse l
                 ≡ reverse (l ++ [ x ] ++ r)
  reverse-++-lemma [] x [] = refl (x :: [])
  reverse-++-lemma [] x (l :: ls) = ap (λ a → a ++ [ l ]) (reverse-++-lemma [] x ls)
  reverse-++-lemma (r :: rs) x [] = ap (λ y → y ++ [ x ]) (reverse-++-lemma rs r [])
  reverse-++-lemma (r :: rs) x (l :: ls) =
   (reverse rs ++ [ r ]) ++ (x :: reverse ls ++ [ l ])     ≡⟨ refl _ ⟩
   (reverse rs ++ [ r ]) ++ ([ x ] ++ reverse ls ++ [ l ]) ≡⟨ refl _ ⟩
   (reverse (r :: rs)) ++ ([ x ] ++ reverse ls) ++ [ l ]   ≡⟨ sym (++-assoc (reverse (r :: rs)) ( x :: reverse ls) [ l ]) ⟩
   (reverse (r :: rs) ++ [ x ] ++ reverse ls) ++ [ l ]     ≡⟨ ap (λ z → z ++ [ l ]) (reverse-++-lemma (r :: rs) x ls) ⟩
   reverse (ls ++ (x :: r :: rs)) ++ [ l ]                 ∎


  flatten-mirror-is-reverse-flatten
    : {A : Type} → flatten {A} ∘ mirror ∼ reverse ∘ flatten
  flatten-mirror-is-reverse-flatten leaf = refl []
  flatten-mirror-is-reverse-flatten (branch x l r)
    =   flatten (mirror r) ++ (x :: flatten (mirror l))
                ≡⟨ ap (λ z → z ++ (x :: flatten (mirror l))) (flatten-mirror-is-reverse-flatten r)  ⟩
        (reverse (flatten r)) ++ (x :: flatten (mirror l))
                 ≡⟨ ap (λ z → (reverse (flatten r)) ++ (x :: z)) (flatten-mirror-is-reverse-flatten l) ⟩
        reverse (flatten r) ++ (x :: (reverse (flatten l)))
                 ≡⟨ reverse-++-lemma (flatten r) x (flatten l) ⟩
        reverse (flatten l ++ (x :: flatten r)) ∎


  module first-approach (X : Type) (s : StrictTotalOrder X ) where

    open StrictTotalOrder s

    all-smaller : BT X → X → Type
    all-smaller leaf x = 𝟙
    all-smaller (branch x l r) y = (x < y) × all-smaller l y × all-smaller r y

    all-bigger : BT X → X → Type
    all-bigger leaf y = 𝟙
    all-bigger (branch x l r) y = (x > y) × all-bigger l y × all-bigger r y

    is-bst : BT X → Type
    is-bst leaf = 𝟙
    is-bst (branch x l r) = all-smaller l x
                          × all-bigger r x
                          × is-bst l
                          × is-bst r

    BST : Type
    BST = Σ t ꞉ BT X , is-bst t

    _∈ₛ'_ : X → BST → Type
    x ∈ₛ' (t , p) = x ∈ t -- this is ineffiecient as it will search the whole tree to find the x

    -- This is a type hence the capital T at the start, this is different from the normal trichotomy
    Trichotomy : X → X → Type
    Trichotomy x y = (x < y) ∔ (x ≡ y) ∔ (x > y)

    _∈ₛ-bst_ : X → BT X → Type

    ∈ₛ-branch : (y x : X) (l r : BT X) → Trichotomy x y → Type
    ∈ₛ-branch y x l r (inl      x<y)  = y ∈ₛ-bst r
    ∈ₛ-branch y x l r (inr (inl x≡y)) = 𝟙
    ∈ₛ-branch y x l r (inr (inr x>y)) = y ∈ₛ-bst l

    y ∈ₛ-bst leaf = 𝟘
    y ∈ₛ-bst branch x l r = ∈ₛ-branch y x l r (trichotomy x y)
    --this is very similar to using with trichotomy but instead we are passing the type

    _∈ₛ_ : X → BST → Type
    x ∈ₛ (t , _) = x ∈ₛ-bst t

    membership-implies-membership' : (y : X) (t : BT X) (i : is-bst t)
                                   → y ∈ₛ (t , i) → y ∈ₛ' (t , i)
    membership-implies-membership' y (branch x l r) (s , b , il , ir) y∈t = goal (trichotomy x y) y∈t
      where
        goal : (trich : Trichotomy x y)
             → ∈ₛ-branch y x l r trich
             → y ∈ (branch x l r)
        goal (inl      x<y)  y∈r = inr (inr (membership-implies-membership' y r ir y∈r))
        goal (inr (inl x≡y)) y∈t = inl (sym x≡y)
        goal (inr (inr x>y)) y∈l = inr (inl (membership-implies-membership' y l il y∈l))

    being-in-is-decidable : (y : X) (t : BT X) → is-decidable (y ∈ₛ-bst t)
    being-in-is-decidable y leaf = 𝟘-is-decidable
    being-in-is-decidable y (branch x l r) = goal (trichotomy x y)
      where
        goal : (trich : Trichotomy x y) → is-decidable (∈ₛ-branch y x l r trich)
        goal (inl      x<y)  = being-in-is-decidable y r
        goal (inr (inl x≡y)) = 𝟙-is-decidable
        goal (inr (inr x>y)) = being-in-is-decidable y l


    insert' : X → BT X → BT X

    insert'-branch
      : (y x : X) (l r : BT X) → Trichotomy x y → BT X
    insert'-branch y x l r (inl      x<y)  = branch x l (insert' y r)
    insert'-branch y x l r (inr (inl x≡y)) = branch x l r
    insert'-branch y x l r (inr (inr x>y)) = branch x (insert' y l) r

    insert' y leaf           = branch y leaf leaf  
    insert' y (branch x l r) = insert'-branch y x l r (trichotomy x y)

    insert'-preserves-all-smaller : (y x : X) (t : BT X)
                                  → y < x
                                  → all-smaller t x
                                  → all-smaller (insert' y t) x
    insert'-preserves-all-smaller y x leaf y<x b = y<x , ⋆ , ⋆
    insert'-preserves-all-smaller y x (branch z l r) y<x (z<x , sl , sr) = goal (trichotomy z y)
      where
        goal : (trich : Trichotomy z y) → all-smaller (insert'-branch y z l r trich) x
        goal (inl z<y) = z<x , sl , insert'-preserves-all-smaller y x r y<x sr  
        goal (inr (inl z≡y)) = z<x , sl , sr
        goal (inr (inr z>y)) = z<x , insert'-preserves-all-smaller y x l y<x sl , sr

    insert'-preserves-all-bigger : (y x : X) (t : BT X)
                                 → y > x
                                 → all-bigger t x
                                 → all-bigger (insert' y t) x
    insert'-preserves-all-bigger y x leaf y>x b = y>x , ⋆ , ⋆
    insert'-preserves-all-bigger y x (branch z l r) y<x (z>x , bl , br) = goal (trichotomy z y)
      where
        goal : (trich : Trichotomy z y) → all-bigger (insert'-branch y z l r trich) x
        goal (inl z<y) = z>x , bl , insert'-preserves-all-bigger y x r y<x br
        goal (inr (inl z≡y)) = z>x , bl , br
        goal (inr (inr z>y)) = z>x , insert'-preserves-all-bigger y x l y<x bl , br


    insert'-preserves-being-bst
       : (y : X) (t : BT X) → is-bst t → is-bst (insert' y t)
    insert'-preserves-being-bst y leaf i = ⋆ , ⋆ , ⋆ , ⋆
    insert'-preserves-being-bst y (branch x l r) (sl , br , il , ir) = goal (trichotomy x y)
      where
        goal : (trich : Trichotomy x y) → is-bst (insert'-branch y x l r trich)
        goal (inl x<y) = sl , insert'-preserves-all-bigger y x r x<y br , il , insert'-preserves-being-bst y r ir
        goal (inr (inl x≡y)) = sl , br , il , ir
        goal (inr (inr x>y)) = insert'-preserves-all-smaller y x l x>y sl  , br , insert'-preserves-being-bst y l il , ir

    insert : X → BST → BST
    insert x (t , i) = insert' x t , insert'-preserves-being-bst x t i


    all-smaller-is-decidable : (t : BT X) (x : X) → is-decidable (all-smaller t x)
    all-smaller-is-decidable leaf y = 𝟙-is-decidable
    all-smaller-is-decidable (branch x l r) y
                             = ×-preserves-decidability (<-is-decidable x y)
                                  (×-preserves-decidability (all-smaller-is-decidable l y ) (all-smaller-is-decidable r y))

    all-bigger-is-decidable : (t : BT X) (x : X) → is-decidable (all-bigger t x)
    all-bigger-is-decidable leaf y = 𝟙-is-decidable
    all-bigger-is-decidable (branch x l r) y
      = ×-preserves-decidability (<-is-decidable y x)
             (×-preserves-decidability (all-bigger-is-decidable l y) (all-bigger-is-decidable r y) )

    being-bst-is-decidable : (t : BT X) → is-decidable (is-bst t)
    being-bst-is-decidable leaf = 𝟙-is-decidable
    being-bst-is-decidable (branch x l r)
      = ×-preserves-decidability (all-smaller-is-decidable l x)
              (×-preserves-decidability (all-bigger-is-decidable r x)
                    (×-preserves-decidability (being-bst-is-decidable l) (being-bst-is-decidable r) ))

    insert'-property₀ : (x : X) (t : BT X) (i : is-bst t)
                      → x ∈ₛ (t , i)
                      → fst (insert x (t , i)) ≡ t
    insert'-property₀ x (branch y l r) (sl , br , il , ir) x∈t = goal (trichotomy y x) x∈t
      where
        goal : (trich : Trichotomy y x) → ∈ₛ-branch x y l r trich → insert'-branch x y l r trich ≡ branch y l r
        goal (inl y<x) x∈ₛt = ap (λ f → branch y l f) (insert'-property₀ x r ir x∈ₛt)
        goal (inr (inl y≡x)) x∈ₛt = refl _
        goal (inr (inr y>x)) x∈ₛt = ap (λ f → branch y f r) (insert'-property₀ x l il x∈ₛt)


    ∈ₛ-branch-left : (x y : X) (l r : BT X)
                   → (trich : Trichotomy y x)
                   → y > x
                   → x ∈ₛ-bst l
                   → ∈ₛ-branch x y l r trich
    ∈ₛ-branch-left x y l r (inl x>y) x<y x∈ₛl =  𝟘-nondep-elim ((irreflexive x) (transitive x<y x>y))
    ∈ₛ-branch-left x y l r (inr (inl x≡y)) x<y x∈ₛl = ⋆
    ∈ₛ-branch-left x y l r (inr (inr x<y')) x<y x∈ₛl = x∈ₛl

    ∈ₛ-branch-left' : (x y : X) (l r : BT X)
                    → (trich : Trichotomy y x)
                    → y > x
                    → ∈ₛ-branch x y l r trich
                    → x ∈ₛ-bst l
    ∈ₛ-branch-left' x y l r (inl y<x) y>x x∈ₛl = 𝟘-nondep-elim ((irreflexive x) (transitive y>x y<x))
    ∈ₛ-branch-left' x y l r (inr (inl y≡x)) y>x x∈ₛl = 𝟘-nondep-elim ((irreflexive' x y (sym y≡x)) y>x)
    ∈ₛ-branch-left' x y l r (inr (inr y>x)) _ x∈ₛl = x∈ₛl

    ∈ₛ-branch-middle : (x y : X) (l r : BT X)
                     → (trich : Trichotomy y x)
                     → y ≡ x
                     → ∈ₛ-branch x y l r trich
    ∈ₛ-branch-middle x y l r (inl y<x) y≡x = 𝟘-nondep-elim ((irreflexive' y x y≡x) y<x)
    ∈ₛ-branch-middle x y l r (inr (inl y≡x)) _ = ⋆
    ∈ₛ-branch-middle x y l r (inr (inr y>x)) y≡x = 𝟘-nondep-elim ((irreflexive' x y (sym y≡x)) y>x)

    ∈ₛ-branch-right : (x y : X) (l r : BT X)
                    → (trich : Trichotomy y x)
                    → y < x
                    → x ∈ₛ-bst r
                    → ∈ₛ-branch x y l r trich
    ∈ₛ-branch-right x y l r (inl y<x) y_ x∈r = x∈r
    ∈ₛ-branch-right x y l r (inr (inl y≡x)) y<x x∈r = ⋆
    ∈ₛ-branch-right x y l r (inr (inr y>x)) y<x x∈r = 𝟘-nondep-elim ((irreflexive x)(transitive y>x y<x))

    ∈ₛ-branch-right' : (x y : X) (l r : BT X)
                     → (trich : Trichotomy y x)
                     → y < x
                     → ∈ₛ-branch x y l r trich
                     → x ∈ₛ-bst r
    ∈ₛ-branch-right' x y l r (inl y<x) _ x∈r = x∈r
    ∈ₛ-branch-right' x y l r (inr (inl y≡x)) y<x x∈r = 𝟘-nondep-elim ((irreflexive' y x y≡x) y<x)
    ∈ₛ-branch-right' x y l r (inr (inr y>x)) y<x x∈r = 𝟘-nondep-elim ((irreflexive x)(transitive y>x y<x))

    insert'-property₁ : (x : X) (t : BT X) (i : is-bst t)  
                      → x ∈ₛ insert x (t , i)
    insert'-property₁ x leaf i =  goal (trichotomy x x) 
      where
        goal : (trich : Trichotomy x x) → ∈ₛ-branch x x leaf leaf trich
        goal (inl x<x) = 𝟘-nondep-elim ((irreflexive x) x<x)
        goal (inr (inl x≡x)) = ⋆
        goal (inr (inr x>x)) = (irreflexive x) x>x
    insert'-property₁ x (branch y l r) (sl , br , il , ir) =  goal (trichotomy y x)
      where
        goal : (trich : Trichotomy y x) → x ∈ₛ-bst insert'-branch x y l r trich 
        goal (inl y<x) =  ∈ₛ-branch-right x y l (insert' x r) (trichotomy y x) y<x (insert'-property₁ x r ir) 
        goal (inr (inl y≡x)) = ∈ₛ-branch-middle x y l r (trichotomy y x) y≡x
        goal (inr (inr y>x)) = ∈ₛ-branch-left x y (insert' x l) r (trichotomy y x) y>x (insert'-property₁ x l il) 

    insert'-property₂ : (x y : X) (t : BT X) (i : is-bst t)
                      → y ∈ₛ insert x (t , i)
                      → (y ≡ x) ∔ (y ∈ₛ (t , i))
    insert'-property₂ x y leaf i y∈ₛt = goal (trichotomy x y) y∈ₛt
      where
        goal : (trich : Trichotomy x y)
             → ∈ₛ-branch y x leaf leaf trich
             → (y ≡ x) ∔ 𝟘
        goal (inl      x<y)  = λ z → inr z
        goal (inr (inl x≡y)) = λ _ → inl (sym x≡y)
        goal (inr (inr x>y)) = λ z → inr z
    insert'-property₂ x y (branch z l r) (sl , br , il , ir) y∈ₛt = goal (trichotomy z y) (trichotomy z x) y∈ₛt
      where
        goal : (trich₁ : Trichotomy z y) → (trich₂ : Trichotomy z x)
             → y ∈ₛ-bst insert'-branch x z l r trich₂
             → (y ≡ x) ∔ ∈ₛ-branch y z l r trich₁ 
        goal (inl      z<y) (inl       z<x) y∈ₛt
          = insert'-property₂ x y r ir (∈ₛ-branch-right' y z l (insert' x r) (trichotomy z y) z<y y∈ₛt)
        goal (inl      z<y) (inr (inl z≡x)) y∈ₛt
          = inr (∈ₛ-branch-right' y z l r (trichotomy z y) z<y y∈ₛt)
        goal (inl      z<y) (inr (inr z>x)) y∈ₛt
          = inr (∈ₛ-branch-right' y z (insert' x l) r (trichotomy z y) z<y y∈ₛt)
        goal (inr (inl z≡y)) (inl      z<x) y∈ₛt
          = inr ⋆
        goal (inr (inr z>y)) (inl      z<x) y∈ₛt
          = inr (∈ₛ-branch-left' y z l (insert' x r) (trichotomy z y) z>y y∈ₛt)
        goal (inr (inl z≡y)) (inr (inl z≡x)) y∈ₛt
          = inr ⋆
        goal (inr (inl z≡y)) (inr (inr z>x)) y∈ₛt
          = inr ⋆
        goal (inr (inr z>y)) (inr (inl z≡x)) y∈ₛt
          = inr (∈ₛ-branch-left' y z l r (trichotomy z y) z>y y∈ₛt)
        goal (inr (inr z>y)) (inr (inr z>x)) y∈ₛt
          = insert'-property₂ x y l il (∈ₛ-branch-left' y z (insert' x l) r (trichotomy z y) z>y y∈ₛt) 

    insert'-property₃ : (x : X) (t : BT X) (i : is-bst t)
                      → (size (fst (insert x (t , i))) ≡ size t)
                      ∔ (size (fst (insert x (t , i))) ≡ size t + 1)
    insert'-property₃ x leaf ⋆ = inr (refl 1)
    insert'-property₃ x (branch y l r) (sl , br , il , ir) = γ (trichotomy y x)
      where
        γ : (trich : Trichotomy y x)
          → (size (insert'-branch x y l r trich) ≡ suc (size l + size r))
          ∔ (size (insert'-branch x y l r trich) ≡ suc((size l + size r) + 1))
        γ (inl y<x) with (insert'-property₃ x r ir)
        ... | inl p = inl (ap suc (ap (λ z → size l + z) p)) 
        ... | inr q = inr (ap suc
                              (trans (ap (λ z → size l + z) q)
                                     (sym (+-assoc (size l) (size r) 1))))
        γ (inr (inl y≡x)) = inl (refl _)
        γ (inr (inr y>x)) with insert'-property₃ x l il
        ... | inl p = inl (ap suc (ap (λ z → z + size r) p))
        ... | inr q = inr (ap suc  ((trans (ap (_+ size r) q)
                                          (trans (ap (_+ size r) (+-comm (size l) 1))
                                                (+-comm 1 (size l + size r))))))
                                     

```
