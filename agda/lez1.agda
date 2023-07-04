infixl -1 _$_
_$_ : {A B : Set} → (A → B) → A → B
fn $ a = fn a

data Bool : Set where
  true  : Bool
  false : Bool

_∧_ : Bool → Bool → Bool
true ∧ true = true
_ ∧ _       = false 

_∨_ : Bool → Bool → Bool
false ∨ false = false
_ ∨ _         = true 

! : Bool → Bool
! true  = false
! false = true

is-tautology₁ : (Bool → Bool) → Bool
is-tautology₁ f = f true ∧ f false

is-tautology₂ : (Bool → Bool → Bool) → Bool
is-tautology₂ f = is-tautology₁ (f true) ∧ is-tautology₁ (f false)

data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero   + b = b
succ n + b = succ (n + b)

one = succ zero
two = succ one 
three = succ two
four = succ three

_*_ : ℕ → ℕ → ℕ
zero   * b = zero
succ n * b = b + (n * b)

six = three * two
seven = succ six

twelve = four * three

half : ℕ → ℕ
half zero            = zero
half (succ zero)     = zero 
half (succ (succ n)) = succ (half n)

test₁ = half (succ (succ (succ zero)))

pred : ℕ → ℕ
pred zero     = zero
pred (succ n) = n

_-_ : ℕ → ℕ → ℕ
a - zero     = a
a - (succ n) = pred (a - n)

test₂ = (three + four) - two

_-₁_ : ℕ → ℕ → ℕ
a -₁ zero            = a
zero -₁ _            = zero
(succ a) -₁ (succ b) = a -₁ b

eq? : ℕ → ℕ → Bool
eq? zero zero         = true
eq? (succ a) (succ b) = eq? a b
eq? _ _               = false 

_≤_ : ℕ → ℕ → Bool
zero   ≤ b      = true
succ a ≤ succ b = a ≤ b
succ a ≤ zero   = false

even? : ℕ → Bool
even? zero     = true
even? (succ n) = ! (even? n)

data Never : Set where
  foo : Never → Never

data Even : ℕ → Set where
  base-even : Even zero
  step-even : {n : ℕ} → Even n → Even (succ (succ n))

data Odd : ℕ → Set where
  base-odd : Odd (succ zero)
  step-odd : {n : ℕ} → Odd n → Odd (succ (succ n))

lemma-sum-even : {a b : ℕ} → Even a → Even b → Even (a + b)
lemma-sum-even base-even     y = y
lemma-sum-even (step-even a) y = step-even $ lemma-sum-even a y

lemma-succ-even : {a : ℕ} → Even a → Odd (succ a)
lemma-succ-even base-even     = base-odd
lemma-succ-even (step-even p) = step-odd $ lemma-succ-even p

lemma-succ-odd : {a : ℕ} → Odd a → Even (succ a)
lemma-succ-odd base-odd     = step-even base-even
lemma-succ-odd (step-odd p) = step-even $ lemma-succ-odd p  

lemma-sum-mixed : {a b : ℕ} → Odd a → Odd b → Even (a + b)
lemma-sum-mixed base-odd     p₂  = lemma-succ-odd p₂
lemma-sum-mixed (step-odd p₁) p₂ = step-even $ lemma-sum-mixed p₁ p₂

data _⨄_ (A B : Set) : Set where
  left  : A → A ⨄ B
  right : B → A ⨄ B

lemma-even-odd : (n : ℕ) → Even n ⨄ Odd n
lemma-even-odd zero             = left  $ base-even
lemma-even-odd (succ zero)      = right $ base-odd
lemma-even-odd (succ (succ n₁)) with lemma-even-odd n₁
... | left  x = left  $ step-even x
... | right y = right $ step-odd  y

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

sum : List ℕ → ℕ
sum []       = zero
sum (x ∷ xs) = x + sum xs 

map : {A B : Set} → (A → B) → List A → List B
map _ []        = []
map fn (x ∷ xs) = (fn x) ∷ (map fn xs)

data Vector (A : Set) : ℕ → Set where
  []  : Vector A zero
  _∷_ : {n : ℕ} → A → Vector A n → Vector A (succ n)

lengthV : {n : ℕ} { A : Set} → Vector A n → ℕ
lengthV []       = zero
lengthV (x ∷ xs) = succ $ lengthV xs

mapV : {n : ℕ} {A B : Set} → (A → B) → Vector A n → Vector B n
mapV _ [] = []
mapV fn (x ∷ xs) = (fn x) ∷ (mapV fn xs)

dropV : {n : ℕ} {A : Set} → (k : ℕ) → Vector A (k + n) → Vector A n
dropV zero xs            = xs
dropV (succ k₁) (x ∷ xs) = dropV k₁ xs 

data ⊥ : Set where

¬ : Set → Set 
¬ X = X → ⊥

infix 5 _≡_

data _≡_ {X : Set} : X → X → Set where
  refl : {a : X} → a ≡ a

{-# BUILTIN EQUALITY _≡_ #-}

dni : {A : Set} → A → ¬ (¬ A)
--                A → (A → ⊥) → ⊥
dni p fn = fn p

contrapposition : {A B : Set} → (A → B) → (¬ B → ¬ A)
contrapposition f p a = p $ f a

de-morgan₁ : {A B : Set} → ¬ (A ⨄ B) → ¬ A
de-morgan₁ fn a = fn $ left a 

de-morgan₂ : {A B : Set} → ¬ (A ⨄ B) → ¬ B
de-morgan₂ fn b = fn $ right b

cong : {A B : Set} {x y : A} → (f : A → B) → x ≡ y → f x ≡ f y
cong f refl = refl

symm : {A : Set} {x y : A} → x ≡ y → y ≡ x
symm refl = refl