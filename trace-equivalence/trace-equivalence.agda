
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

data _≡_ {A : Set} : A → A → Set where
  refl : {a : A} → a ≡ a

data ⊥ : Set where

¬ : (A : Set) → Set
¬ A = A → ⊥


module TraceEquivalence
  {℘ : Set → Set}
  (_∈_ : {A : Set} → A → ℘ A → Set)
  (_∉_ : {A : Set} → A → ℘ A → Set)
  (contains : {A : Set} (s : ℘ A) (a : A) → (a ∈ s) ⨄ (a ∉ s)) where


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
    
    step-ren  : {a : Channel} {p p₁ : Proc} {f : Channel → Channel} → Step p (↑ a) p₁ → Step (p [ f ]) (↑ (f a)) (p₁ [ f ]) 
    step-ren-τ  : {p p₁ : Proc} {f : Channel → Channel} → Step p τ p₁ → Step (p [ f ]) τ (p₁ [ f ])  


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

  ⇒-sum : {p q r : Proc} → p ⊆Tr q → (p + r) ⊆Tr (q + r)
  ⇒-sum pq t∈p+r with ←-trace-sum t∈p+r
  ... | left  p-path = →-trace-sum₁ (pq p-path)
  ... | right r-path = →-trace-sum₂ r-path

  comp-sum : {p q r : Proc} → p ≡Tr q → (p + r) ≡Tr (q + r)
  comp-sum (pq ⇔ qp) = ⇒-sum pq ⇔ ⇒-sum qp

  -- restriction

  restriction : Trace → ℘ Channel → Trace
  restriction ε l = ε
  restriction (τ ∷ w) l = τ ∷ restriction w l
  restriction ((↑ a) ∷ w) l with contains l a
  ... | left  a∈l = ε
  ... | right a∉l = (↑ a) ∷ (restriction w l)

  ←-trace-res : {t : Trace} {p : Proc} {l : ℘ Channel} → t ∈Tr p → (restriction t l) ∈Tr (p ∖ l)
  ←-trace-res {ε} t∈p = ε-trace
  ←-trace-res {τ ∷ w} {p} {l} (∷-trace step w∈p₁) = ∷-trace (step-res-τ step) (←-trace-res w∈p₁)
  ←-trace-res {(↑ a) ∷ w} {p} {l} (∷-trace step w∈p₁) with contains l a
  ... | left  a∈l = ε-trace
  ... | right a∉l = ∷-trace (step-res a∉l step) (←-trace-res w∈p₁)

  lemma-restriction : {a : Channel} {l : ℘ Channel} {w : Trace} → a ∉ l → restriction (↑ a ∷ w) l ≡ (↑ a ∷ restriction w l)
  lemma-restriction a∉l = {! refl  !}

  →-trace-res : {s : Trace} {p : Proc} {l : ℘ Channel} → s ∈Tr (p ∖ l) → ∃[ t ] ((t ∈Tr p) × ((restriction t l) ≡ s))
  →-trace-res ε-trace = ⟨ ε , [ ε-trace , refl ] ⟩
  →-trace-res {τ ∷ w} (∷-trace (step-res-τ step) wpl) with →-trace-res wpl
  ... | ⟨ s₁ , [ s∈p₁ , refl ] ⟩ = ⟨ τ ∷ s₁ , [ ∷-trace step s∈p₁ , refl ] ⟩
  →-trace-res {(↑ a) ∷ w} (∷-trace (step-res a∉l step) wpl) with →-trace-res wpl
  ... | ⟨ s₁ , [ s∈p₁ , refl ] ⟩ = ⟨ (↑ a) ∷ s₁ , [ ∷-trace step s∈p₁ , lemma-restriction a∉l ] ⟩

  ⇒-res : {p q : Proc} {l : ℘ Channel} → p ⊆Tr q → (p ∖ l) ⊆Tr (q ∖ l)
  ⇒-res pq tpl with →-trace-res tpl 
  ... | ⟨ t , [ t∈p , refl ] ⟩ = ←-trace-res (pq t∈p)

  comp-res : {p q : Proc} {l : ℘ Channel} → p ≡Tr q → (p ∖ l) ≡Tr (q ∖ l)
  comp-res (pq ⇔ qp) = ⇒-res pq ⇔ ⇒-res qp

  -- Renaming - relabeling

  rename : Trace → (Channel → Channel) → Trace
  rename ε _           = ε
  rename (τ ∷ w) f     = τ ∷ (rename w f)
  rename ((↑ a) ∷ w) f = (↑ (f a)) ∷ (rename w f)

  ←-trace-ren : {t : Trace} {f : Channel → Channel} {p : Proc} → t ∈Tr p → (rename t f) ∈Tr (p [ f ])
  ←-trace-ren ε-trace = ε-trace
  ←-trace-ren {τ ∷ w} (∷-trace step w∈p)     = ∷-trace (step-ren-τ step) (←-trace-ren w∈p)
  ←-trace-ren {(↑ a) ∷ w} (∷-trace step w∈p) = ∷-trace (step-ren step) (←-trace-ren w∈p)

  →-trace-ren : {s : Trace} {f : Channel → Channel} {p : Proc} → s ∈Tr (p [ f ]) → ∃[ t ] ((t ∈Tr p) × (s ≡ rename t f))
  →-trace-ren ε-trace = ⟨ ε , [ ε-trace , refl ] ⟩
  →-trace-ren {τ ∷ w} (∷-trace (step-ren-τ step) s∈pf) with →-trace-ren s∈pf
  ... | ⟨ s₁ , [ s₁∈p₁ , refl ] ⟩ = ⟨ τ ∷ s₁ , [ ∷-trace step s₁∈p₁ , refl ] ⟩
  →-trace-ren {(↑ a) ∷ w} (∷-trace (step-ren {g} step) s∈pf) with →-trace-ren s∈pf
  ... | ⟨ s₁ , [ s₁∈p₁ , refl ] ⟩ = ⟨ ↑ g ∷ s₁ , [ ∷-trace step s₁∈p₁ , refl ] ⟩

  ⇒-ren : {p q : Proc} {f : Channel → Channel} → p ⊆Tr q → (p [ f ]) ⊆Tr (q [ f ])
  ⇒-ren pq s∈pf with →-trace-ren s∈pf
  ... | ⟨ t , [ t∈p , refl ] ⟩ = ←-trace-ren (pq t∈p)

  comp-ren : {p q : Proc} {f : Channel → Channel} → p ≡Tr q → (p [ f ]) ≡Tr (q [ f ])
  comp-ren (pq ⇔ qp) = ⇒-ren pq ⇔ ⇒-ren qp