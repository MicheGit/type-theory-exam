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

  -- lemma-head : (x y : A) (ys : OList) → y ≤ head ys → y ≤ x → y ≤ head 

  insert : A → OList → OList
  insert x nil                = cons x nil ≤max
  insert x (cons y ys y≤head) with cmp x y
  ... | left  x≤y = cons x (cons y ys y≤head) x≤y
  ... | right y≤x = cons y (insert x ys) {!   !}
