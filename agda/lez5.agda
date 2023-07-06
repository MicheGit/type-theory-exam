infixl -1 _$_
_$_ : {A B : Set} → (A → B) → A → B
fn $ a = fn a

infixr 5 _∷_

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

single : {A : Set} → A → List A
single x = x ∷ []

data _⨄_ (A B : Set) : Set where
  left  : A → A ⨄ B
  right : B → A ⨄ B

module Implementation
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⨄ (y ≤ x)) where
  
  insert : (a : A) → List A → List A
  insert a []       = single a
  insert a (x ∷ xs) with (cmp a x)
  ... | left  (a≤x) = a ∷ x ∷ xs
  ... | right (x≤a) = x ∷ insert a xs

  sort : List A → List A
  sort []       = []
  sort (x ∷ xs) = insert x (sort xs)

module Verification
  {A : Set}
  (_≤_ : A → A → Set)
  (cmp : (x y : A) → (x ≤ y) ⨄ (y ≤ x)) where

  open Implementation _≤_ cmp

  data IsOrdered : List A → Set where
    empty     : IsOrdered []
    singleton : {x : A} → IsOrdered (x ∷ [])
    cons      : {x y : A} {ys : List A} → x ≤ y → IsOrdered (y ∷ ys) → IsOrdered (x ∷ y ∷ ys)

  lemma₀ : (x y : A) (ys : List A) → y ≤ x → IsOrdered (y ∷ ys) → IsOrdered(y ∷ insert x ys)
  lemma₀ x y []       y≤x p = cons y≤x singleton 
  lemma₀ x y (z ∷ ys) y≤x (cons y≤z oz) with cmp x z
  ... | left  x≤z = cons y≤x (cons x≤z oz)
  ... | right z≤x = cons y≤z (lemma₀ x z ys z≤x oz)

  lemma : (x : A) (ys : List A) → IsOrdered ys → IsOrdered (insert x ys)
  lemma x []       p = singleton
  lemma x (y ∷ ys) p with cmp x y
  ... | left  x≤y = cons x≤y p           -- IsOrdered x ∷ y ∷ ys
  ... | right y≤x = lemma₀ x y ys y≤x p  -- IsOrdered y ∷ insert x ys

  theorem : (xs : List A) → IsOrdered (sort xs)
  theorem []       = empty
  theorem (x ∷ xs) = lemma x (sort xs) ((theorem xs))
