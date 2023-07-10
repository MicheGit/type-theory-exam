data ℕ : Set where
  zero : ℕ
  succ : ℕ → ℕ

data List (A : Set) : Set where
  []  : List A
  _∷_ : A → List A → List A

data _×_ (A B : Set) : Set where
  [_,_] : A → B → A × B 

π₁ : {A B : Set} → A × B → A
π₁ [ a , b ] = a

π₂ : {A B : Set} → A × B → B
π₂ [ a , b ] = b

data _∈_ {A : Set} : A → List A → Set where
  head : {a : A} {l : List A} → a ∈ (a ∷ l)
  tail : {a b : A} {l : List A} → a ∈ l → a ∈ (b ∷ l)

data ⊥ : Set where

¬ : Set → Set
¬ A = A → ⊥

data _∉_ {A : Set} : A → List A → Set where

data Act : Set where
  τ : Act

data Trace : Set where
  ε : Trace
  _∷_ : Act → Trace → Trace 

data Proc : Set where
  p : Proc
  q : Proc
  r : Proc
  _∙_ : Act → Proc → Proc 
  _+_ : Proc → Proc → Proc
  _∥_ : Proc → Proc → Proc
  _∖_ : Proc → List Act → Proc
  _[_] : Proc → (Act → Act) → Proc

data Step : Proc → Act → Proc → Set where
  step-act  : {α : Act} {p : Proc} → Step (α ∙ p) α p
  step-sum₁ : {α : Act} {p r p₁ : Proc} → Step p α p₁ → Step (p + r) α p₁
  step-sum₂ : {α : Act} {p r r₁ : Proc} → Step r α r₁ → Step (p + r) α r₁
  step-par₁ : {α : Act} {p r p₁ : Proc} → Step p α p₁ → Step (p ∥ r) α (p₁ ∥ r)
  step-par₂ : {α : Act} {p r r₁ : Proc} → Step r α r₁ → Step (p ∥ r) α (p ∥ r₁)
  step-par₃ : {α : Act} {p p₁ r r₁ : Proc} → Step p α p₁ → Step r α r₁ → Step (p ∥ r) τ (p₁ ∥ r₁)
  step-res  : {α : Act} {l : List Act} {p p₁ : Proc} → α ∉ l → Step p α p₁ → Step (p ∖ l) α (p₁ ∖ l)
  step-ren  : {α : Act} {f : Act → Act} {p p₁ : Proc} → Step p α p₁ → Step (p [ f ]) (f(α)) (p₁ [ f ])

data _∈Tr_ : Trace → Proc → Set where
  ε-trace : {p : Proc} → ε ∈Tr p
  ∷-trace : {p p₁ : Proc} {α : Act} {w : Trace} → (Step p α p₁) → (w ∈Tr p₁) → (α ∷ w) ∈Tr p


data _≡Tr_ (p q : Proc) : Set where
  _⇔_ : ({t : Trace} → t ∈Tr p → t ∈Tr q) → ({t : Trace} → t ∈Tr q → t ∈Tr p) → p ≡Tr q


-- Trace equivalence is compositional

lemma-act : {s : Trace} {p q : Proc} {α : Act} → ({t : Trace} → t ∈Tr p → t ∈Tr q) → s ∈Tr (α ∙ p) → s ∈Tr (α ∙ q)
lemma-act conv ε-trace = ε-trace
lemma-act conv (∷-trace step-act trace) = ∷-trace step-act (conv trace)

comp-act : {p q : Proc} {α : Act} → p ≡Tr q → (α ∙ p) ≡Tr (α ∙ q)
comp-act (pq ⇔ qp) = lemma-act pq ⇔ lemma-act qp

comp-sum : {p q r : Proc} → p ≡Tr q → (p + r) ≡Tr (q + r)
comp-sum (pq ⇔ qp) = {!   !} ⇔ {!   !}

