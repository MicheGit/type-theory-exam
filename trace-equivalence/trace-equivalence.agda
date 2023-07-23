
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

{-
Context:
  CCS (Calculus of Communicating Systems) is a language describing systems which perform
    some sort of computing and may communicate between each other.

  A process, in CCS can be seen as a finite state automata, therefor it is 
    always associated to a state. Processes can perform two kinds of actions:
    - communication over a channel;
    - an internal state transition.
    Communication is always done over a channel.

  CCS can be used to describe both processes' behaviour and specifcation.
    Therefore, the correctness of a process is some sort of equivalence between processes.
  
  There are different kinds of equivalence. Trace Equivalencce is one of them, and states
    that two processes are equivalent when their set of finite traces is the same.
    A trace is defined as a finite sequence of actions of a process from its initial state.

  The formal definition is as follows.

  Let P a process, Tr(P) = { α Tr(P') | P -α→ P' } ∪ { ε }

  In other words:
  - the empty trace ε belongs to any process;
  - a trace αw belongs to the traces of P when P can perform the action α and becoming P'; 
    and w is a trace of P'.

  An important property of equivalences is that they are congruences. In CCS this concerns
    the semantic rules of the processes, which are:
    - action: α.P is a process that performs the action α and then behaves as P;
    - nondeterministic sum: P + R is a process that can behaves as P or R;
    - parallel composition: each action of P | R is an action of P or R, wich change state
      independently; but there is also the chance that they might communicate and perform a
      a step in sync: this is only allowed (but not forced!) when they may communicate over
      the same channel;
    - restriction: given a set L of channels, P ∖ L behaves as P, except that it can't 
      communicate over any channel in L;
    - renaming / relabeling: given a renaming function f: Channel → Channel then P[f] behaves
      as P but any communication is forwarded over the function f. 

  To prove that an equivalence is also a congruence, we need to show that it is compositional,
    that means:
    (i)   - Tr(P) ≡ Tr(Q) implies Tr(α.P)   ≡ Tr(α.Q)
    (ii)  - Tr(P) ≡ Tr(Q) implies Tr(P + R) ≡ Tr(Q + R)
    (iii) - Tr(P) ≡ Tr(Q) implies Tr(P | R) ≡ Tr(Q | R)
    (iv)  - Tr(P) ≡ Tr(Q) implies Tr(P ∖ L) ≡ Tr(Q ∖ L)
    (v)   - Tr(P) ≡ Tr(Q) implies Tr(P[f])  ≡ Tr(Q[f])
-}


module TraceEquivalence
  {℘ : Set → Set}
  {empty : {A : Set} → ℘ A}
  {singleton : {A : Set} → A → ℘ A}
  {_∪_ : {A : Set} → ℘ A → ℘ A → ℘ A}
  {unions : {A : Set} → ℘ (℘ A) → ℘ A}
  (map : {A B : Set} → (A → B) → ℘ A → ℘ B)
  (_∈_ : {A : Set} → A → ℘ A → Set)
  (_∉_ : {A : Set} → A → ℘ A → Set)
  (contains : {A : Set} (s : ℘ A) (a : A) → (a ∈ s) ⨄ (a ∉ s)) where

  -- No representation of channels is needed.
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
    _∙_ : Channel → Proc → Proc       -- c ∙ P can communicate over a channel c
                                      -- and then it behaves as P
    _+_ : Proc → Proc → Proc          -- P + Q can behave as P or Q
    _∥_ : Proc → Proc → Proc          -- P ∥ Q composes P and Q in a single process
                                      -- allowing those two processes to communicate
                                      -- with each other
    _∖_ : Proc → ℘ Channel → Proc     -- P ∖ L can communicate only in channels that
                                      -- are not in L
    _[_] : Proc → (Channel → Channel) → Proc  -- P [ f ] redirects all communication as specified by f 


  -- Structural Operational Semantics for CCS processes  
  data Step : Proc → Act → Proc → Set where
    step-act   : {c : Channel} {p : Proc} → Step (c ∙ p) (↑ c) p
                                      
    step-sum₁  : {a : Act} {p q p₁ : Proc} → Step p a p₁ → Step (p + q) a p₁
    step-sum₂  : {a : Act} {p q q₁ : Proc} → Step q a q₁ → Step (p + q) a q₁

    step-par₁  : {a : Act} {p q p₁ : Proc} → Step p a p₁ → Step (p ∥ q) a (p₁ ∥ q)
    step-par₂  : {a : Act} {p q q₁ : Proc} → Step q a q₁ → Step (p ∥ q) a (p ∥ q₁)
    step-par₃  : {c : Channel} {p q p₁ q₁ : Proc} → Step p (↑ c) p₁ → Step q (↑ c) q₁ → Step (p ∥ q) τ (p₁ ∥ q₁)
    
    step-res   : {c : Channel} {l : ℘ Channel} {p p₁ : Proc} → c ∉ l → Step p (↑ c) p₁ → Step (p ∖ l) (↑ c) (p₁ ∖ l)
    step-res-τ : {l : ℘ Channel} {p p₁ : Proc} → Step p τ p₁ → Step (p ∖ l) τ (p₁ ∖ l)
    
    step-ren   : {c : Channel} {f : Channel → Channel} {p p₁ : Proc} → Step p (↑ c) p₁ → Step (p [ f ]) (↑ (f c)) (p₁ [ f ]) 
    step-ren-τ : {f : Channel → Channel} {p p₁ : Proc} → Step p τ p₁ → Step (p [ f ]) τ (p₁ [ f ])  


  -- A trace belongs to a process if:
  -- - it is empty;
  -- - or its head is an action that that process migh do, and the tail is a trace of the 
  --    process result of that step.
  data _∈Tr_ : Trace → Proc → Set where
    ε-trace : {p : Proc} → ε ∈Tr p
    ∷-trace : {a : Act} {w : Trace} {p p₁ : Proc} → (Step p a p₁) → (w ∈Tr p₁) → (a ∷ w) ∈Tr p


  _⊆Tr_ : (p q : Proc) → Set
  p ⊆Tr q = {t : Trace} → t ∈Tr p → t ∈Tr q


  -- two sets of traces are the same if
  -- forall trace t, if it belongs to the first set then it belongs to the second one,
  -- and vice versa
  data _≡Tr_ (p q : Proc) : Set where
    _⇔_ : (p ⊆Tr q) → (q ⊆Tr p) → p ≡Tr q

  -- Proof
  -- The proof is divided in five sections, one per composition possible.
  -- Each section, except for the first have a similar structure:
  -- 1. first we define a type or a function such that it's easy to verify the equivalence 
  --    given Tr(P) ≡ Tr(Q)
  -- 2. then we show that such representation is equivalent to the set of traces of a process
  -- 3. then we combine all those lemmas to prove that if a trace belongs to the composition 
  --    of P it also belongs to the composition of Q
  -- 4. finally the equivalence is shown by switching sides in (3.) 

  -- (i) Action
  -- The action rule simply adds an action at the beginning of each trace
  -- of a process. 
  ⇒-act : {p q : Proc} {a : Channel} → p ⊆Tr q → (a ∙ p) ⊆Tr (a ∙ q)
  ⇒-act pq ε-trace = ε-trace
  ⇒-act pq (∷-trace step-act w∈p) = ∷-trace step-act (pq w∈p)

  comp-act : {p q : Proc} {a : Channel} → p ≡Tr q → (a ∙ p) ≡Tr (a ∙ q)
  comp-act (pq ⇔ qp) = ⇒-act pq ⇔ ⇒-act qp

  -- (ii) Sum
  -- We need to show that set of traces of P + R is the union of the traces of the two processes,
  -- i.e.:
  -- - if a trace belongs to P + R then it belongs to P or R
  -- - if a trace belongs to P or R then it belongs to P + R
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

  -- (iii) Parallel composition

  -- We need this lemma. For all traces t of P then for any process R 
  --  P | R can perform the trace t. Simply put, the composition might perform
  --  only steps of P.
  lemma-par-ε₁ : {t : Trace} {p r : Proc} → t ∈Tr p → t ∈Tr (p ∥ r)
  lemma-par-ε₁ ε-trace = ε-trace
  lemma-par-ε₁ (∷-trace step t∈p₁) = ∷-trace (step-par₁ step) (lemma-par-ε₁ t∈p₁)

  lemma-par-ε₂ : {t : Trace} {p r : Proc} → t ∈Tr r → t ∈Tr (p ∥ r)
  lemma-par-ε₂ ε-trace = ε-trace
  lemma-par-ε₂ (∷-trace step t∈r₁) = ∷-trace (step-par₂ step) (lemma-par-ε₂ t∈r₁)

  -- Putting in parallel traces gives as output a set of traces,
  --  later we show that this set is equivalent to the traces 
  --  suitable for the parallel composition rules.
  data ∈Par : Trace → Trace → Trace → Set where
    empty-tp : {t : Trace} → ∈Par t ε t
    empty-tr : {t : Trace} → ∈Par t t ε
    p-path   : {a : Act} {w s z : Trace} → ∈Par z w s → ∈Par (a ∷ z) (a ∷ w) s
    r-path   : {g : Act} {w s z : Trace} → ∈Par z w s → ∈Par (g ∷ z) w (g ∷ s)
    τ-path   : {c : Channel} {w s z : Trace} → ∈Par z w s → ∈Par (τ ∷ z) ((↑ c) ∷ w) ((↑ c) ∷ s)

  ←-trace-par : {t tp tr : Trace} {p r : Proc} → tp ∈Tr p → tr ∈Tr r → ∈Par t tp tr → t ∈Tr (p ∥ r)
  ←-trace-par tp∈p tr∈r empty-tp = lemma-par-ε₂ tr∈r
  ←-trace-par tp∈p tr∈r empty-tr = lemma-par-ε₁ tp∈p
  ←-trace-par (∷-trace step-p w∈p₁) tr∈r (p-path t∈par) = ∷-trace (step-par₁ step-p) (←-trace-par w∈p₁ tr∈r t∈par)
  ←-trace-par tp∈p (∷-trace step-r w∈r₁) (r-path t∈par) = ∷-trace (step-par₂ step-r) (←-trace-par tp∈p w∈r₁ t∈par)
  ←-trace-par (∷-trace step-p w∈p₁) (∷-trace step-r w∈r₁) (τ-path t∈par) = ∷-trace (step-par₃ step-p step-r) (←-trace-par w∈p₁ w∈r₁ t∈par)

  →-trace-par : {t : Trace} {p r : Proc} → t ∈Tr (p ∥ r) → ∃[ tp ] (∃[ tr ] (((tp ∈Tr p) × (tr ∈Tr r)) × ∈Par t tp tr) )
  →-trace-par ε-trace = ⟨ ε , ⟨ ε , [ [ ε-trace , ε-trace ] , empty-tp ] ⟩ ⟩
  →-trace-par (∷-trace {a} (step-par₁ step-p) w∈rest) with →-trace-par w∈rest
  ... | ⟨ tp₁ , ⟨ tr , [ [ tp₁∈p₁ , tr∈r ] , inpar ] ⟩ ⟩ = ⟨ a ∷ tp₁ , ⟨ tr , [ [ ∷-trace step-p tp₁∈p₁ , tr∈r ] , p-path inpar ] ⟩ ⟩
  →-trace-par (∷-trace {a} (step-par₂ step-r) w∈rest) with →-trace-par w∈rest 
  ... | ⟨ tp , ⟨ tr₁ , [ [ tp∈p , tr₁∈r₁ ] , inpar ] ⟩ ⟩ = ⟨ tp , ⟨ a ∷ tr₁ , [ [ tp∈p , ∷-trace step-r tr₁∈r₁ ] , r-path inpar ] ⟩ ⟩
  →-trace-par (∷-trace (step-par₃ {c} step-p step-r) w∈rest) with →-trace-par w∈rest 
  ... | ⟨ tp₁ , ⟨ tr₁ , [ [ tp₁∈p₁ , tr₁∈r₁ ] , inpar ] ⟩ ⟩ = ⟨ (↑ c) ∷ tp₁ , ⟨ (↑ c) ∷ tr₁ , [ [ ∷-trace step-p tp₁∈p₁ , ∷-trace step-r tr₁∈r₁ ] , τ-path inpar ] ⟩ ⟩

  ⇒-par : {p q r : Proc} → p ⊆Tr q → (p ∥ r) ⊆Tr (q ∥ r)
  ⇒-par pq w∈p∥r with →-trace-par w∈p∥r
  ... | ⟨ tp , ⟨ tr , [ [ tp∈p , tr∈r ] , inpar ] ⟩ ⟩ = ←-trace-par (pq tp∈p) tr∈r inpar

  comp-par : {p q r : Proc} → p ≡Tr q → (p ∥ r) ≡Tr (q ∥ r)
  comp-par (pq ⇔ qp) = ⇒-par pq ⇔ ⇒-par qp  

  -- (iv) Restriction

  -- We define a restricted trace as the equivalent of a trace of P mapped to
  --  P ∖ L. This means removing all traces that would be blocked by L.
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

  →-trace-res : {s : Trace} {l : ℘ Channel} {p : Proc} → s ∈Tr (p ∖ l) → ∃[ t ] ((t ∈Tr p) × ((restriction t l) ≡ s))
  →-trace-res ε-trace = ⟨ ε , [ ε-trace , refl ] ⟩
  →-trace-res {τ ∷ w} (∷-trace (step-res-τ step) wpl) with →-trace-res wpl
  ... | ⟨ s₁ , [ s∈p₁ , refl ] ⟩ = ⟨ τ ∷ s₁ , [ ∷-trace step s∈p₁ , refl ] ⟩
  →-trace-res {(↑ a) ∷ w} {l} (∷-trace (step-res _ step) wpl) with →-trace-res wpl
  ... | ⟨ s₁ , [ s∈p₁ , refl ] ⟩ with contains l a
  ...   | right a∉l = ⟨ (↑ a) ∷ s₁ , [ ∷-trace step s∈p₁ , {!   !} ] ⟩ -- refl

  ⇒-res : {p q : Proc} {l : ℘ Channel} → p ⊆Tr q → (p ∖ l) ⊆Tr (q ∖ l)
  ⇒-res pq tpl with →-trace-res tpl 
  ... | ⟨ t , [ t∈p , refl ] ⟩ = ←-trace-res (pq t∈p)

  comp-res : {p q : Proc} {l : ℘ Channel} → p ≡Tr q → (p ∖ l) ≡Tr (q ∖ l)
  comp-res (pq ⇔ qp) = ⇒-res pq ⇔ ⇒-res qp

  -- (v) Renaming

  -- The renaming function simply renames all channels used applying that function
  --  to each element of the list, with the exection of τ.
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
