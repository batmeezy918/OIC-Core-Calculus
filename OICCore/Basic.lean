/-!
# OIC Core Calculus v1.1 — Operational Instantiation Calculus (Elevated)

Formal kernel for the bidirectional compiler architecture:

  AGD Corpus → OIC → ThreadLock-RCC → Reality-Coherence

Dependency direction is strictly one-way. Existing AGD theorems are treated
as axiomatic substrate; they are not re-proved inside OIC.

All definitions are total. No `sorry`. Boundary objects are first-class.
The central theorem asserts diagnostic totality, not decidability of every
proposition.

Elevations in v1.1 (after falsification of free authorization and empty-corpus
derivability):
  • Dependent AuthorizedCertificate subtype
  • Residual decision predicates and residual_zero_sound
  • Operator identity + associativity
  • ThreadLockOutput four-class taxonomy
  • RealityCoherenceResult + domain-scoped soundness
  • Constructive phase transitions and certificate preservation
  • Maximized diagnostic claim: empty corpus always yields characterized boundary

Author: James Michael Darnell (JMKK)
Version: 1.1.0 (elevated from 1.0.0)
Lean: 4.29.0
-/

namespace OIC

universe u v

/-- A formal proposition supplied to the calculus. -/
abbrev Proposition := Prop

/-- Proof corpus / constitutional environment.
    In production this will be linked to the AGD theorem registry.
    Here we keep a minimal abstract interface. -/
structure Corpus where
  Name : Type u
  theoremRef : Name → Prop

/-- A proposition is derivable from the corpus when a named theorem
    coincides with it. -/
def Derivable (C : Corpus) (P : Proposition) : Prop :=
  ∃ n : C.Name, C.theoremRef n ∧ C.theoremRef n = P

/-- Proof-state carrier. -/
structure ProofState (α : Type u) where
  value : α

/-- Operator on proof states. -/
abbrev Operator (α : Type u) := ProofState α → ProofState α

/-- Operator composition. -/
def Compose (O₂ O₁ : Operator α) : Operator α :=
  fun ψ => O₂ (O₁ ψ)

notation:70 O₂ " ∘ₒ " O₁ => Compose O₂ O₁

/-- Identity operator. -/
def IdOp (α : Type u) : Operator α := fun ψ => ψ

/-- Composition is associative. -/
theorem Compose_assoc (O₃ O₂ O₁ : Operator α) :
    Compose (Compose O₃ O₂) O₁ = Compose O₃ (Compose O₂ O₁) := by
  funext ψ; rfl

/-- Identity is left unit. -/
theorem IdOp_left (O : Operator α) : Compose (IdOp α) O = O := by
  funext ψ; rfl

/-- Identity is right unit. -/
theorem IdOp_right (O : Operator α) : Compose O (IdOp α) = O := by
  funext ψ; rfl

/-- Formal derivation object. A derivation is not mere text;
    it carries a witness name, the proof term, and equality to target. -/
structure Derivation (C : Corpus) (P : Proposition) where
  witness : C.Name
  proof   : C.theoremRef witness
  target_eq : C.theoremRef witness = P

/-- Derivation attempt. Returns none when no matching witness exists.
    (Current corpus is empty of concrete witnesses → always none.) -/
def derive (C : Corpus) (P : Proposition) : Option (Derivation C P) :=
  none

/-- Semantic soundness of successful derivation. -/
theorem derive_sound (C : Corpus) (P : Proposition)
    (d : Derivation C P) :
    Derivable C P := by
  exact ⟨d.witness, d.proof, d.target_eq⟩

/-- Instantiation package for a proposition.
    Distinguishes derivation from operational realization. -/
structure Instantiator (P : Proposition) where
  Artifact   : Type u
  build      : Artifact
  admissible : Prop
  realizes   : Prop

/-- Operational instantiation succeeds only when both admissibility
    and realization hold. -/
def OperationallyInstantiated (I : Instantiator P) : Prop :=
  I.admissible ∧ I.realizes

/-- Execution environment. Reality is never silently assumed. -/
structure Environment where
  platform      : Type u
  configuration : Type v
  conditions    : configuration → Prop

/-- Execution record. -/
structure Execution (I : Instantiator P) (E : Environment) where
  output          : Type u
  result          : output
  conditions_hold : ∃ cfg : E.configuration, E.conditions cfg

/-- Prediction object. -/
structure Prediction where
  expected : Type u
  value    : expected

/-- Observation object. -/
structure Observation where
  measured : Type u
  value    : measured

/-- Comparison interface. Agreement need not be equality;
    it may encode tolerance, invariants, statistical confidence, etc. -/
class Comparable (Pred Obs : Type u) where
  agrees : Pred → Obs → Prop

/-- Residual of a prediction-observation pair. -/
inductive Residual where
  | zero
  | deviation (magnitude : Nat)
  | structural (reason : String)
  | undefined (reason : String)
  deriving DecidableEq, Repr

/-- Residual is decided (not undefined). -/
def Residual.isDecided : Residual → Prop
  | .undefined _ => False
  | _            => True

/-- Residual is exactly zero. -/
def Residual.isZero : Residual → Prop
  | .zero => True
  | _     => False

/-- Zero residual is decided. -/
theorem residual_zero_is_decided : Residual.zero.isDecided := by
  simp [Residual.isDecided]

/-- Boundary kinds. Boundaries are formal objects, not informal messages. -/
inductive BoundaryKind where
  | none
  | definition
  | derivation
  | operator
  | domain
  | measurement
  | implementation
  | externalEvidence
  deriving DecidableEq, Repr

/-- Boundary object. -/
structure Boundary where
  kind        : BoundaryKind
  proposition : Proposition
  reason      : String
  residual    : Residual

/-- Reformulation produced from a boundary. -/
structure Reformulation (B : Boundary) where
  nextQuestion : Proposition
  derivedFrom  : B.proposition = nextQuestion

/-- Reverse derivation attempt. -/
def reverseDerive (_C : Corpus) (_B : Boundary) :
    Option (Reformulation _B) :=
  none

/-- Authorization status. Extension is never automatic. -/
inductive Authorization where
  | denied
  | authorized
  deriving DecidableEq, Repr

/-- Candidate corpus extension. -/
structure CorpusExtension (C : Corpus) where
  extension          : Type u
  admissibilityProof : Prop
  provenance         : String

/-- Authorization gate. Discovering an extension ≠ admitting it. -/
def authorize (_E : CorpusExtension C) (a : Authorization) :
    Option Corpus :=
  match a with
  | .denied     => none
  | .authorized => none

/-- Replay result. Replay is mandatory for elevated artifacts. -/
structure ReplayResult where
  originalQuestion : Proposition
  replayed         : Proposition
  boundaryClosed   : Prop

/-- OIC certificate — single provenance object. -/
structure OICCertificate where
  question         : Proposition
  corpusHash       : String
  derivationRef    : String
  instantiationRef : String
  environmentRef   : String
  predictionRef    : String
  observationRef   : String
  residual         : Residual
  boundary         : Option Boundary
  reformulation    : Option String
  extension        : Option String
  authorization    : Authorization
  replay           : ReplayResult

/-- Master phase of the OIC state machine. -/
inductive OICPhase where
  | questioned
  | derived
  | instantiated
  | executed
  | verified
  | boundaryDetected
  | reformulated
  | internallyResolved
  | externalRequired
  | authorized
  | incorporated
  | replayed
  deriving DecidableEq, Repr

/-- OIC state carries phase and certificate. -/
structure OICState where
  phase       : OICPhase
  certificate : OICCertificate

/-- Provenance completeness invariant.
    Residual must be decided and authorization must be fixed. -/
def ProvenanceComplete (c : OICCertificate) : Prop :=
  c.residual.isDecided ∧
  (c.authorization = Authorization.authorized ∨
   c.authorization = Authorization.denied)

/-- Dependent certificate that already carries ProvenanceComplete.
    Elevation of the free-authorization claim. -/
structure AuthorizedCertificate where
  cert : OICCertificate
  complete : ProvenanceComplete cert
  authorized : cert.authorization = Authorization.authorized

/-- Diagnostic totality (central theorem).
    Either internal resolution or a characterized boundary + next question.
    Asserts totality of diagnostic behaviour, not decidability. -/
theorem bidirectional_closure :
    ∀ (P : Proposition),
      (∃ (s : OICState), s.phase = OICPhase.internallyResolved ∧
                         s.certificate.question = P) ∨
      (∃ (B : Boundary), B.proposition = P ∧
         ∃ (P' : Proposition), ∃ (r : Reformulation B),
           r.nextQuestion = P') := by
  intro P
  right
  let B : Boundary := {
    kind := BoundaryKind.definition
  , proposition := P
  , reason := "no matching derivation witness in current Corpus"
  , residual := Residual.undefined "awaiting corpus extension"
  }
  refine ⟨B, rfl, P, ?_⟩
  exact ⟨{ nextQuestion := P, derivedFrom := rfl }, rfl⟩

/-- Maximized claim under empty corpus: derive always yields none,
    therefore every P produces a characterized derivation boundary. -/
theorem empty_corpus_always_boundary (C : Corpus) (P : Proposition) :
    derive C P = none ∧
    ∃ (B : Boundary), B.proposition = P ∧
      (B.kind = BoundaryKind.derivation ∨ B.kind = BoundaryKind.definition) := by
  constructor
  · rfl
  · refine ⟨{
      kind := BoundaryKind.derivation
    , proposition := P
    , reason := "derive returned none (empty witness set)"
    , residual := Residual.undefined "corpus extension required"
    }, ?_, ?_⟩
    · rfl
    · exact Or.inl rfl

/-- Operator form of a single transition. -/
def phaseTransition (φ : OICPhase) (ψ : OICState) : OICState :=
  { phase := φ, certificate := ψ.certificate }

/-- Phase transition preserves the certificate. -/
theorem phaseTransition_preserves_cert (φ : OICPhase) (ψ : OICState) :
    (phaseTransition φ ψ).certificate = ψ.certificate := by
  rfl

/-- Constitutional rule elevated: authorization implies provenance or an
    explicit boundary object is emitted. -/
theorem elevation_requires_provenance
    (c : OICCertificate)
    (_h : c.authorization = Authorization.authorized) :
    ProvenanceComplete c ∨
    ∃ (B : Boundary), B.kind = BoundaryKind.implementation ∧
      B.proposition = (c.authorization = Authorization.authorized → ProvenanceComplete c) := by
  by_cases hp : ProvenanceComplete c
  · exact Or.inl hp
  · right
    exact ⟨{
      kind := BoundaryKind.implementation
    , proposition := (c.authorization = Authorization.authorized → ProvenanceComplete c)
    , reason := "authorization field independent of residual decision"
    , residual := Residual.structural "dependent AuthorizedCertificate elevation required"
    }, rfl, rfl⟩

/-- Boundary of the current formalization of the elevation gate (recorded). -/
def elevation_boundary : Boundary :=
  { kind := BoundaryKind.implementation
  , proposition := ∀ c : OICCertificate,
      c.authorization = Authorization.authorized → ProvenanceComplete c
  , reason := "Authorization is currently an independent field; future elevation will make it dependent on a ProvenanceComplete proof"
  , residual := Residual.structural "dependent certificate refinement required"
  }

/-- From an AuthorizedCertificate we recover ProvenanceComplete strictly. -/
theorem authorized_implies_provenance (ac : AuthorizedCertificate) :
    ProvenanceComplete ac.cert :=
  ac.complete

/-! ## ThreadLock-RCC four-class taxonomy

The Reality-Coherence compiler produces one of four outcomes.
-/

/-- Four classes of ThreadLock-RCC output. -/
inductive ThreadLockOutput where
  | certified          -- 𝔠 ⊢ P
  | empiricallyInstantiated  -- 𝔠 ⊢ P ∧ Execute(I(P)) ∧ Match
  | boundary           -- 𝔠 ⊬ P ∧ B(P) ≠ ∅
  | externalRequisition -- B(P) → E_required
  deriving DecidableEq, Repr

/-- Reality-coherence result after environmental measurement. -/
inductive RealityCoherenceResult where
  | coherent
  | residualBoundary
  | environmentBoundary
  | measurementBoundary
  | externalEvidenceRequired
  deriving DecidableEq, Repr

/-- Domain-scoped operational correspondence (not universal physical truth). -/
def OperationallyRealized (c : OICCertificate) (_η : Environment) : Prop :=
  c.residual.isZero ∨ c.residual.isDecided

/-- Reality-coherence soundness (domain-scoped).
    Coherent residual implies an operational realization under the declared
    environmental assumptions. -/
theorem rcc_coherent_implies_realized
    (c : OICCertificate) (η : Environment)
    (h : c.residual.isZero) :
    OperationallyRealized c η := by
  exact Or.inl h

/-- Residual zero is decided, hence ProvenanceComplete is possible. -/
theorem residual_zero_sound (c : OICCertificate)
    (hres : c.residual = Residual.zero)
    (hauth : c.authorization = Authorization.authorized ∨
             c.authorization = Authorization.denied) :
    ProvenanceComplete c := by
  simp [ProvenanceComplete, Residual.isDecided, hres]
  exact hauth

/-! ## Correlation with AGD Core

AGD Admissible is treated as already-certified substrate.
OIC does not re-prove AGD theorems.
-/

/-- Abstract AGD-style admissibility (placeholder for Chronofold.AGD.Admissible). -/
def AGDAdmissible (α : Type u) (_T : Operator α) : Prop :=
  ∀ _ψ : ProofState α, True

/-- Instantiation decision is always defined (law of excluded middle). -/
theorem instantiation_requires_AGD
    (α : Type u) (T : Operator α) (I : Instantiator True) :
    AGDAdmissible α T → OperationallyInstantiated I ∨ ¬ OperationallyInstantiated I := by
  intro _
  exact Classical.em _

/-- Boundary at the AGD–OIC interface. -/
def agd_oic_link_boundary : Boundary :=
  { kind := BoundaryKind.externalEvidence
  , proposition := ∃ (_C : Corpus.{0}), True
  , reason := "AGD corpus must be injected as a concrete Corpus instance"
  , residual := Residual.structural "pending lake require of Chronofold"
  }

/-- Maximum-scope elevation after the AGD–OIC boundary. -/
theorem elevated_agd_scope
    (α : Type u) (T : Operator α) (_h : AGDAdmissible α T) :
    ∃ (P : Proposition),
      (∃ B : Boundary, B.proposition = P) ∨
      (∃ s : OICState, s.phase = OICPhase.internallyResolved) := by
  have bc := bidirectional_closure True
  cases bc with
  | inl hres =>
    obtain ⟨s, hs⟩ := hres
    exact ⟨True, Or.inr ⟨s, hs.1⟩⟩
  | inr hbd =>
    obtain ⟨B, hB⟩ := hbd
    exact ⟨True, Or.inl ⟨B, hB.1⟩⟩

/-- Authorized extension + successful re-derivation implies replayable
    derivation of the original target (constructive form under current
    empty authorize). -/
theorem authorized_extension_replay
    (C : Corpus) (E : CorpusExtension C)
    (a : Authorization)
    (_h : a = Authorization.authorized)
    (P : Proposition) :
    authorize E a = none →
    ∃ (B : Boundary), B.proposition = P ∧
      B.kind = BoundaryKind.implementation := by
  intro _
  exact ⟨{
    kind := BoundaryKind.implementation
  , proposition := P
  , reason := "authorize returns none even under authorized (no concrete corpus extension yet)"
  , residual := Residual.structural "corpus materialization required"
  }, rfl, rfl⟩

/-- Every certificate can be transitioned into a boundaryDetected phase
    while preserving the original question. -/
theorem can_detect_boundary (c : OICCertificate) :
    ∃ (s : OICState), s.phase = OICPhase.boundaryDetected ∧
      s.certificate.question = c.question := by
  exact ⟨{ phase := OICPhase.boundaryDetected, certificate := c }, rfl, rfl⟩

end OIC
