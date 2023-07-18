
data _⨄_ (A B : Set) : Set where
  left  : A → A ⨄ B
  right : B → A ⨄ B

data _×_ (A B : Set) : Set where
  [_,_] : A → B → A × B

π₁ : {A B : Set} → A × B → A
π₁ [ a , b ] = a

π₂ :  {A B : Set} → A × B → B
π₂ [ a , b ] = b

data Σ (A : Set) (B : A → Set) : Set where
  ⟨_,_⟩ : (x : A) → B x → Σ A B

Σ-syntax = Σ
infix 2 Σ-syntax
syntax Σ-syntax A (λ x → Bx) = Σ[ x ∈ A ] Bx

∃ : ∀ {A : Set} (B : A → Set) → Set
∃ {A} B = Σ A B

∃-syntax = ∃
syntax ∃-syntax (λ x → B) = ∃[ x ] B

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
  singleton : {a : A} → a ∈ ⟨ a ⟩
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
  
  step-sum₁ : {p q p₁ : Proc} {a : Act} → Step p a p₁ → Step (p + q) a p₁
  step-sum₂ : {p q q₁ : Proc} {a : Act} → Step q a q₁ → Step (p + q) a q₁

  step-par₁ : {p q p₁ : Proc} {a : Channel} → Step p (↑ a) p₁ → Step (p ∥ q) (↑ a) (p₁ ∥ q)
  step-par₂ : {p q q₁ : Proc} {a : Channel} → Step q (↑ a) q₁ → Step (p ∥ q) (↑ a) (p ∥ q₁)
  step-par₃ : {p q p₁ q₁ : Proc} {a : Channel} → Step p (↑ a) p₁ → Step q (↑ a) q₁ → Step (p ∥ q) τ (p₁ ∥ q₁)
  
  step-res  : {p p₁ : Proc} {a : Channel} {l : ℘ Channel} → a ∉ l → Step p (↑ a) p₁ → Step (p ∖ l) (↑ a) (p₁ ∖ l)
  step-res-τ : {p p₁ : Proc} {l : ℘ Channel} → Step p τ p₁ → Step (p ∖ l) τ (p₁ ∖ l)
  
  step-ren  : {p p₁ : Proc} {a : Channel} {f : Channel → Channel} → Step p (↑ a) p₁ → Step (p [ f ]) (↑ (f a)) (p₁ [ f ])  


step-sum-inv : {p q r : Proc} {a : Channel} → Step (p + q) (↑ a) r → (Step p (↑ a) r) ⨄ (Step q (↑ a) r)
step-sum-inv (step-sum₁ step) = left step
step-sum-inv (step-sum₂ step) = right step 

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

←-trace-sum : {t : Trace} {p r : Proc} → t ∈Tr (p + r) → (t ∈Tr p) ⨄ (t ∈Tr r)
←-trace-sum ε-trace = left ε-trace
←-trace-sum (∷-trace (step-sum₁ p-step) trace) = left (∷-trace p-step trace)
←-trace-sum (∷-trace (step-sum₂ r-step) trace) = right (∷-trace r-step trace)

→-trace-sum₁ : {t : Trace} {p r : Proc} → t ∈Tr p → t ∈Tr (p + r)
→-trace-sum₁ ε-trace = ε-trace
→-trace-sum₁ (∷-trace step trace) = ∷-trace (step-sum₁ step) trace

→-trace-sum₂ : {t : Trace} {p r : Proc} → t ∈Tr r → t ∈Tr (p + r)
→-trace-sum₂ ε-trace = ε-trace
→-trace-sum₂ (∷-trace step trace) = ∷-trace (step-sum₂ step) trace

trace-sum : Trace → Trace → ℘ Trace
trace-sum t s = ⟨ t ⟩ ∪ ⟨ s ⟩

trace-sum-⇒-sum : {tp tr : Trace} {p r : Proc} → tp ∈Tr p → tr ∈Tr r → ({t : Trace} → t ∈ (trace-sum tp tr) → t ∈Tr (p + r))  
trace-sum-⇒-sum tp∈p tr∈r (i-∪-left  singleton) = →-trace-sum₁ tp∈p
trace-sum-⇒-sum tp∈p tr∈r (i-∪-right singleton) = →-trace-sum₂ tr∈r

sum-⇒-trace-sum : {t : Trace} {p r : Proc} → t ∈Tr (p + r) → ∃[ tp ] (∃[ tr ] (((tp ∈Tr p) × (tr ∈Tr r)) × (t ∈ (trace-sum tp tr))))
sum-⇒-trace-sum {t} {p} {r} trace with ←-trace-sum trace
... | left  p-trace = ⟨ t , ⟨ ε , [ [ p-trace , ε-trace ] , (i-∪-left singleton) ] ⟩ ⟩
... | right r-trace = ⟨ ε , ⟨ t , [ [ ε-trace , r-trace ] , (i-∪-right singleton) ] ⟩ ⟩

⇒-sum : {p q r : Proc} → p ⊆Tr q → (p + r) ⊆Tr (q + r)
⇒-sum pq t∈p+r with ←-trace-sum t∈p+r
... | left  p-path = →-trace-sum₁ (pq p-path)
... | right r-path = →-trace-sum₂ r-path

comp-sum : {p q r : Proc} → p ≡Tr q → (p + r) ≡Tr (q + r)
comp-sum (pq ⇔ qp) = ⇒-sum pq ⇔ ⇒-sum qp

-- restriction

←-trace-res-a : {p p₁ : Proc} {a : Channel} {l : ℘ Channel} → Step (p ∖ l) (↑ a) (p₁ ∖ l) → (Step p (↑ a) p₁) × (a ∉ l)
←-trace-res-a (step-res x step) = [ step , x ]

←-trace-res-τ : {p p₁ : Proc} {l : ℘ Channel} → Step (p ∖ l) τ (p₁ ∖ l) → Step p τ p₁
←-trace-res-τ (step-res-τ step) = step

⇒-res : {p q : Proc} {l : ℘ Channel} → p ⊆Tr q → (p ∖ l) ⊆Tr (q ∖ l)
⇒-res pq ε-trace = ε-trace
⇒-res pq (∷-trace (step-res a∉l step) w∈p₁) = {!   !}
⇒-res pq (∷-trace (step-res-τ step) w∈p₁) = ∷-trace (step-res-τ {!   !}) {! ⇒-res pq w∈p₁  !}

comp-res : {p q : Proc} {l : ℘ Channel} → p ≡Tr q → (p ∖ l) ≡Tr (q ∖ l)
comp-res (pq ⇔ qp) = ⇒-res pq ⇔ ⇒-res qp