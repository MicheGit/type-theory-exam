data List (A : Set) : Set where
  []  : List A 
  _∷_ : A → List A → List A

data _⨄_ (A B : Set) : Set where
  left  : A → A ⨄ B
  right : B → A ⨄ B


module CorrectByConstruction
  {A : Set} 
  (_≤_ : A → A → Set)
  (max : A)
  (≤max : {x : A} → x ≤ max)
  (cmp : (x y : A) → (x ≤ y) ⨄ (y ≤ x))
  where

  data OList : Set

  head : OList → A

  data OList where
    nil  : OList
    cons : (x : A) (xs : OList) → x ≤ head xs → OList
  
  head nil          = max
  head (cons x _ _) = x

  insert : A → OList → OList
  insert x nil                = cons x nil ≤max
  insert x (cons y ys y≤head) with cmp x y
  ... | left  x≤y = cons x (cons y ys y≤head) x≤y
  ... | right y≤x with insert x ys
  ...     | nil = cons y nil ≤max
  ...     | cons z zs z≤head with cmp y z
  ...         | left  y≤z = cons y (cons z zs z≤head) y≤z
  ...         | right z≤y = cons z nil ≤max

  sort : List A → OList
  sort []       = nil
  sort (x ∷ xs) = insert x (sort xs) 
 