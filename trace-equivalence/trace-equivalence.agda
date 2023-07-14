data ℘ (A : Set) : Set where
  ∅ : ℘ A
  ⟨_⟩ : A → ℘ A
  _∪_ : ℘ A → ℘ A → ℘ A
  _∩_ : ℘ A → ℘ A → ℘ A

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

data ⊥ : Set where

¬ : (A : Set) → Set
¬ A = A → ⊥

_≢_ : {A : Set} → A → A → Set
a ≢ b = ¬ (a ≡ b)

data _∈_ {A : Set} : A → ℘ A → Set where
  singleton : {a b : A} → a ≡ b → a ∈ ⟨ b ⟩
  i-∪-left  : {a : A} {s t : ℘ A} → a ∈ s → a ∈ (s ∪ t)
  i-∪-right : {a : A} {s t : ℘ A} → a ∈ t → a ∈ (s ∪ t)
  i-∩       : {a : A} {s t : ℘ A} → a ∈ s → a ∈ t → a ∈ (s ∩ t) 

data _∉_ {A : Set} : A → ℘ A → Set where
  empty     : {a : A} → a ∉ ∅
  ∉-single  : {a b : A} → a ≢ b → a ∉ ⟨ b ⟩
  n-∪       : {a : A} {s t : ℘ A} → a ∉ s → a ∉ t → a ∉ (s ∪ t)
  n-∩-left  : {a : A} {s t : ℘ A} → a ∉ s → a ∉ (s ∩ t)
  n-∩-right : {a : A} {s t : ℘ A} → a ∉ t → a ∉ (s ∩ t)

data Channel : Set where

-- In CCS an action might be:
--  - a communication over a certain channel α, γ, etc..
--  - a hidden (internal) state transition (τ)
data Act : Set where
  τ : Act
  ↑ : Channel → Act

-- A (finite / complete) trace is a sequence of actions.
-- It is a way to represent the behaviour of a process.
data Trace : Set where
  ε : Trace
  _∷_ : Act → Trace → Trace 

-- Processes can be represented by a set of possible
--  single-step transitions. Processes may perform
--  some kind of action and then becoming another 
--  process. 
-- 
-- The constructors of Proc, along with the SOS rules
--  defined later, describe the set of possible actions
--  that a process can perform.
data Proc : Set where
  ∅ : Proc                          -- the empty process can perform no action
  _∙_ : Channel → Proc → Proc       -- α ∙ P can communicate over a channel α
                                    -- and then it behaves as P would
  _+_ : Proc → Proc → Proc          -- P + Q can behave as P or Q
  _∥_ : Proc → Proc → Proc          -- P ∥ Q composes P and Q in a single process
                                    -- allowing those two processes to communicate
                                    -- with each other
  _∖_ : Proc → ℘ Channel → Proc     -- P ∖ L can communicate only in channels that
                                    -- are not in L
  _[_] : Proc → (Channel → Channel) → Proc  -- P [ f ] redirects all communication as specified by f 


-- Structural Operational Semantics for CCS processes  
data Step : Proc → Act → Proc → Set where
  step-act  : {p : Proc} {a : Channel} → Step (a ∙ p) (↑ a) p
  step-sum₁ : {p q p₁ : Proc} {a : Channel} → Step p (↑ a) p₁ → Step (p + q) (↑ a) p₁
  step-sum₂ : {p q q₁ : Proc} {a : Channel} → Step q (↑ a) q₁ → Step (p + q) (↑ a) q₁
  step-par₁ : {p q p₁ : Proc} {a : Channel} → Step p (↑ a) p₁ → Step (p ∥ q) (↑ a) (p₁ ∥ q)
  step-par₂ : {p q q₁ : Proc} {a : Channel} → Step q (↑ a) q₁ → Step (p ∥ q) (↑ a) (p ∥ q₁)
  step-par₃ : {p q p₁ q₁ : Proc} {a : Channel} → Step p (↑ a) p₁ → Step q (↑ a) q₁ → Step (p ∥ q) τ (p₁ ∥ q₁)
  step-res  : {p p₁ : Proc} {a : Channel} {l : ℘ Channel} → a ∉ l → Step p (↑ a) p₁ → Step (p ∖ l) (↑ a) (p₁ ∖ l)
  step-ren  : {p p₁ : Proc} {a : Channel} {f : Channel → Channel} → Step p (↑ a) p₁ → Step (p [ f ]) (↑ (f a)) (p₁ [ f ])  


data _∈Tr_ : Trace → Proc → Set where
  ε-trace : {p : Proc} → ε ∈Tr p
  ∷-trace : {p p₁ : Proc} {a : Act} {w : Trace} → (Step p a p₁) → (w ∈Tr p₁) → (a ∷ w) ∈Tr p

_⊆Tr_ : (p q : Proc) → Set
p ⊆Tr q = {t : Trace} → t ∈Tr p → t ∈Tr q

data _≡Tr_ (p q : Proc) : Set where
  _⇔_ : (p ⊆Tr q) → (q ⊆Tr p) → p ≡Tr q

-- Proof

-- Action
⇒-act : {p q : Proc} {a : Channel} → p ⊆Tr q → (a ∙ p) ⊆Tr (a ∙ q)
⇒-act conv ε-trace = ε-trace
⇒-act conv (∷-trace step-act w∈p) = ∷-trace step-act (conv w∈p)

comp-act : {p q : Proc} {a : Channel} → p ≡Tr q → (a ∙ p) ≡Tr (a ∙ q)
comp-act (pq ⇔ qp) = ⇒-act pq ⇔ ⇒-act qp

-- Sum

_∪Tr_ : (p q : Proc) → ℘ Trace
p ∪Tr q = {!   !}

⇒-sum : {p q r : Proc} → p ⊆Tr q → (p + r) ⊆Tr (q + r)
⇒-sum conv ε-trace = ε-trace
⇒-sum conv (∷-trace x trace) = ∷-trace {!   !} {!   !} 

comp-sum : {p q r : Proc} → p ≡Tr q → (p + r) ≡Tr (q + r)
comp-sum (pq ⇔ qp) = ⇒-sum pq ⇔ ⇒-sum qp

