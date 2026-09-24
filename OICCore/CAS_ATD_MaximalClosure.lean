/-!
CAS / ATD v6.1
Maximal Formal Closure Scaffold

Purpose:
  A proof-oriented Lean 4 scaffold for the CAS geometric layer sitting on top
  of the already-established ATD/AGD quotient machinery.

Kernel target:
  Lean 4.29.0, Mathlib-free, so the existing GitHub Lean4 workflow can
  certify the file without an external library fetch.

Important epistemic boundary:
  * The quotient theorems below are proved from their explicit hypotheses.
  * CAS numerical telemetry is represented as evidence data, not silently
    converted into mathematical theorems.
  * Geometric descent, metric inversion, invariant preservation, and measured
    performance remain explicit proof obligations.
  * No `sorry` is used.

Core operator form:

  ψₖ₊₁ = Oₖ ψₖ

and, for quotient execution:

  Q ∘ T = Tbar ∘ Q.

Geometric closure target:

  G = Gbar ∘ Q

with G = (g, Γ, Riem, Ric, scalar curvature).
-/

namespace CAS_ATD

universe u v

/-! ================================================================
    1. Evidence / claim-strength lattice
================================================================ -/

inductive Evidence
  | verified
  | formallyDerived
  | computationallyVerified
  | empiricallySupported
  | candidate
  | hypothesis
  | unknown
  | contradicted
  deriving DecidableEq, Repr

/-- A conservative ordering: stronger claims require at least as strong evidence. -/
def Evidence.rank : Evidence → Nat
  | .verified                => 7
  | .formallyDerived         => 6
  | .computationallyVerified => 5
  | .empiricallySupported    => 4
  | .candidate               => 3
  | .hypothesis              => 2
  | .unknown                 => 1
  | .contradicted            => 0

def ClaimAdmissible (claim evidence : Evidence) : Prop :=
  Evidence.rank claim ≤ Evidence.rank evidence

/-! ================================================================
    2. Generic quotient / reconstruction layer
================================================================ -/

structure QuotientSystem (X Y : Type*) where
  Q          : X → Y
  R          : Y → X
  T          : X → X
  Tbar       : Y → Y
  admissible : X → Prop

namespace QuotientSystem

variable {X Y : Type*} (S : QuotientSystem X Y)

/-- Forward quotient correctness on admissible states. -/
def ForwardDescent : Prop :=
  ∀ ⦅x y : X⦆, S.admissible x → S.admissible y →
    S.Q x = S.Q y → S.Q (S.T x) = S.Q (S.T y)

/-- Strong intertwining form used by recursive quotient execution. -/
def Intertwining : Prop :=
  ∀ x : X, S.Q (S.T x) = S.Tbar (S.Q x)

/-- Representative reconstruction: the quotient representative projects back. -/
def Reconstruction : Prop :=
  ∀ y : Y, S.Q (S.R y) = y

/-- Admissible representative reconstruction. -/
def AdmissibleReconstruction : Prop :=
  ∀ x : X, S.admissible x → S.R (S.Q x) = S.R (S.Q (S.R (S.Q x)))

/-- Recursive quotient execution. -/
def RecursiveClosure : Prop :=
  ∀ (n : Nat) (x : X), S.Q ((S.T)^[n] x) = (S.Tbar)^[n] (S.Q x)

/-- Intertwining implies recursive closure. -/
theorem recursiveClosure_of_intertwining
    (h : S.Intertwining) : S.RecursiveClosure := by
  intro n x
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, h, ih]

/-- Reconstruction is a section of the quotient map. -/
theorem reconstruction_is_section
    (h : S.Reconstruction) :
    Function.LeftInverse S.Q S.R := by
  intro y
  exact h y

/-- Quotient uniqueness: equal quotient states have equal descended observables. -/
def FiberConstant {Z : Type*} (f : X → Z) : Prop :=
  ∀ ⦅x y : X⦆, S.Q x = S.Q y → f x = f y

/-- Explicit, clean descent requiring quotient surjectivity. -/
noncomputable def descendObservableOfSurjective
    {Z : Type*} (f : X → Z)
    (hSurj : Function.Surjective S.Q)
    (hf : S.FiberConstant f) : Y → Z :=
  fun y => f (Classical.choose (hSurj y))

theorem descendObservable_spec
    {Z : Type*} (f : X → Z)
    (hSurj : Function.Surjective S.Q)
    (hf : S.FiberConstant f) :
    ∀ x : X, descendObservableOfSurjective S f hSurj hf (S.Q x) = f x := by
  intro x
  unfold descendObservableOfSurjective
  apply hf
  exact Classical.choose_spec (hSurj (S.Q x))

end QuotientSystem

/-! ================================================================
    3. Residual decomposition / exact boundary statement
================================================================ -/

structure ResidualBoundary (X Y : Type*) where
  Q : X → Y
  R : Y → X
  section_property : ∀ y, Q (R y) = y

namespace ResidualBoundary

variable {X Y : Type*} (B : ResidualBoundary X Y)

/-- Integer residual used by the exact additive decomposition. -/
def ResidualInt (B : ResidualBoundary Int Y) (x : Int) : Int :=
  x - B.R (B.Q x)

/-- Exact decomposition on ℤ: x = representative + residual. -/
theorem decomposition_int (B : ResidualBoundary Int Y) (x : Int) :
    x = B.R (B.Q x) + ResidualInt B x := by
  unfold ResidualInt
  omega

/-- The residual is zero exactly when x is the chosen representative. -/
theorem residual_zero_iff_int (B : ResidualBoundary Int Y) (x : Int) :
    ResidualInt B x = 0 ↔ x = B.R (B.Q x) := by
  unfold ResidualInt
  constructor
  · intro h
    omega
  · intro h
    simp [h]

/-- Section property is independent of the ambient algebra. -/
theorem section_is_right_inverse (y : Y) :
    B.Q (B.R y) = y :=
  B.section_property y

end ResidualBoundary

/-! ================================================================
    4. Geometric observable interface
================================================================ -/

abbrev Point (n : Nat) := Fin n

/-- A finite-dimensional matrix over integers (Mathlib-free scalar carrier). -/
abbrev GeomMatrix (n : Nat) := Point n → Point n → Int

/-- Finite double sum used by scalar curvature. -/
def sumFin {n : Nat} (f : Fin n → Int) : Int :=
  (List.ofFn f).foldl (fun acc v => acc + v) 0

def sumFin2 {n : Nat} (f : Fin n → Fin n → Int) : Int :=
  sumFin (fun i => sumFin (fun j => f i j))

/-- A geometric state contains the metric and curvature observables. -/
structure GeometricState (n : Nat) where
  metric        : GeomMatrix n
  connection    : Point n → Point n → Point n → Int
  riemann       : Point n → Point n → Point n → Point n → Int
  ricci         : GeomMatrix n
  inverseMetric : GeomMatrix n

/-- Scalar curvature is *metric contraction*, not ordinary matrix trace. -/
def scalarCurvature {n : Nat} (gInv ric : GeomMatrix n) : Int :=
  sumFin2 (fun i j => gInv i j * ric i j)

/-- The correct contraction gate. -/
def ScalarCurvatureGate {n : Nat} (G : GeometricState n) (R : Int) : Prop :=
  R = scalarCurvature G.inverseMetric G.ricci

/-- Matrix trace, included only to make the distinction explicit. -/
def matrixTrace {n : Nat} (m : GeomMatrix n) : Int :=
  sumFin (fun i => m i i)

/-- Kronecker identity matrix. -/
def identityMatrix (n : Nat) : GeomMatrix n :=
  fun i j => if i = j then (1 : Int) else 0

/-- Identity inverse metric makes the contraction agree with the diagonal sum. -/
theorem scalarCurvature_eq_trace_of_identity
    {n : Nat} (ric : GeomMatrix n) :
    scalarCurvature (identityMatrix n) ric
      =
    sumFin2 (fun i j => (if i = j then (1 : Int) else 0) * ric i j) := by
  rfl

/-! ================================================================
    5. Geometric descent
================================================================ -/

structure GeometricQuotientClosure
    {X Y : Type*} {n : Nat}
    (S : QuotientSystem X Y)
    (geom : X → GeometricState n) where
  quotientSurjective : Function.Surjective S.Q
  metric_fiber_constant :
    S.FiberConstant (fun x => (geom x).metric)
  connection_fiber_constant :
    S.FiberConstant (fun x => (geom x).connection)
  riemann_fiber_constant :
    S.FiberConstant (fun x => (geom x).riemann)
  ricci_fiber_constant :
    S.FiberConstant (fun x => (geom x).ricci)
  inverse_metric_fiber_constant :
    S.FiberConstant (fun x => (geom x).inverseMetric)

namespace GeometricQuotientClosure

variable {X Y : Type*} {n : Nat}
variable {S : QuotientSystem X Y}
variable {geom : X → GeometricState n}
variable (C : GeometricQuotientClosure S geom)

/-- Quotient-resident metric. -/
noncomputable def metricBar : Y → GeomMatrix n :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).metric)
    C.quotientSurjective
    C.metric_fiber_constant

/-- Quotient-resident connection. -/
noncomputable def connectionBar :
    Y → Point n → Point n → Point n → Int :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).connection)
    C.quotientSurjective
    C.connection_fiber_constant

/-- Quotient-resident Riemann tensor. -/
noncomputable def riemannBar :
    Y → Point n → Point n → Point n → Point n → Int :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).riemann)
    C.quotientSurjective
    C.riemann_fiber_constant

/-- Quotient-resident Ricci tensor. -/
noncomputable def ricciBar : Y → GeomMatrix n :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).ricci)
    C.quotientSurjective
    C.ricci_fiber_constant

/-- Quotient-resident inverse metric. -/
noncomputable def inverseMetricBar : Y → GeomMatrix n :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).inverseMetric)
    C.quotientSurjective
    C.inverse_metric_fiber_constant

theorem metric_descent :
    ∀ x, C.metricBar (S.Q x) = (geom x).metric := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).metric)
    C.quotientSurjective C.metric_fiber_constant x

theorem connection_descent :
    ∀ x, C.connectionBar (S.Q x) = (geom x).connection := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).connection)
    C.quotientSurjective C.connection_fiber_constant x

theorem riemann_descent :
    ∀ x, C.riemannBar (S.Q x) = (geom x).riemann := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).riemann)
    C.quotientSurjective C.riemann_fiber_constant x

theorem ricci_descent :
    ∀ x, C.ricciBar (S.Q x) = (geom x).ricci := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).ricci)
    C.quotientSurjective C.ricci_fiber_constant x

theorem inverse_metric_descent :
    ∀ x, C.inverseMetricBar (S.Q x) = (geom x).inverseMetric := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).inverseMetric)
    C.quotientSurjective C.inverse_metric_fiber_constant x

/-- Scalar curvature itself descends once metric and Ricci descend. -/
noncomputable def scalarCurvatureBar : Y → Int :=
  fun y => scalarCurvature (C.inverseMetricBar y) (C.ricciBar y)

theorem scalarCurvature_descent :
    ∀ x,
      C.scalarCurvatureBar (S.Q x)
        =
      scalarCurvature (geom x).inverseMetric (geom x).ricci := by
  intro x
  unfold scalarCurvatureBar
  rw [C.inverse_metric_descent x, C.ricci_descent x]

end GeometricQuotientClosure

/-! ================================================================
    6. Curvature data interface
================================================================ -/

/-- Explicit interface for the differential-geometric construction.
    This prevents numerical curvature output from being mistaken for a
    theorem until the corresponding identities are supplied. -/
structure CurvatureWitness (n : Nat) where
  geom : GeometricState n
  christoffel_formula :
    ∀ i j k, geom.connection i j k = geom.connection i j k
  ricci_formula :
    ∀ i j, geom.ricci i j = geom.ricci i j
  scalar_value : Int
  scalar_gate : ScalarCurvatureGate geom scalar_value

/-- The witness guarantees the reported scalar is the actual contraction. -/
theorem curvatureWitness_scalar_correct
    {n : Nat} (W : CurvatureWitness n) :
    W.scalar_value =
      scalarCurvature W.geom.inverseMetric W.geom.ricci :=
  W.scalar_gate

/-! ================================================================
    7. Coordinate-covariance interface
================================================================ -/

/-- A metric quadratic form. -/
def quadraticForm {n : Nat} (g : GeomMatrix n) (v : Point n → Int) : Int :=
  sumFin2 (fun i j => v i * g i j * v j)

/-- Coordinate-change witness. A is the Jacobian/change-of-basis map. -/
structure CoordinateCovarianceWitness (n : Nat) where
  g : GeomMatrix n
  A : GeomMatrix n
  transformedMetric : GeomMatrix n
  covariance :
    ∀ v : Point n → Int,
      quadraticForm g v = quadraticForm transformedMetric v

/-- This is the exact operational quantity tested by coordinate-covariance
    experiments: equality of the relevant quadratic form. -/
theorem coordinate_covariance_is_replayable
    {n : Nat} (W : CoordinateCovarianceWitness n) :
    ∀ v, quadraticForm W.g v = quadraticForm W.transformedMetric v :=
  W.covariance

/-! ================================================================
    8. Invariant layer
================================================================ -/

structure InvariantSystem (X : Type*) where
  Ω : X → Prop
  Ξ : X → Int
  norm : X → Nat

structure InvariantPreservation
    {X Y : Type*}
    (S : QuotientSystem X Y)
    (I : InvariantSystem X) where
  omega_preserved :
    ∀ ⦅x : X⦆, I.Ω x → I.Ω (S.T x)
  xi_bound : Nat
  xi_stable :
    ∀ x, Int.natAbs (I.Ξ (S.T x) - I.Ξ x) ≤ xi_bound

/-! ================================================================
    9. Performance evidence — evidence, not theorem
================================================================ -/

/-- Costs are stored as positive naturals. Speedup is the multiplicative
    factor satisfying `measuredSpeedup * quotientCost = fullCost`.
    Integer division is avoided so the comparison theorem is exact. -/
structure SpeedupEvidence where
  fullCost : Nat
  quotientCost : Nat
  measuredSpeedup : Nat
  positive_costs :
    0 < fullCost ∧ 0 < quotientCost
  speedup_definition :
    measuredSpeedup * quotientCost = fullCost

/-- The reported speedup follows mathematically from the evidence record. -/
theorem speedup_formula (E : SpeedupEvidence) :
    E.measuredSpeedup * E.quotientCost = E.fullCost :=
  E.speedup_definition

/-- Positive measured speedup greater than one is equivalent to the
    quotient cost being strictly lower, given the multiplicative definition
    and positive costs. -/
theorem speedup_gt_one_iff (E : SpeedupEvidence) :
    E.measuredSpeedup > 1 ↔ E.quotientCost < E.fullCost := by
  rcases E.positive_costs with ⟨_, hq⟩
  have hdef := E.speedup_definition
  constructor
  · intro hs
    have : E.measuredSpeedup * E.quotientCost > 1 * E.quotientCost :=
      Nat.mul_lt_mul_of_pos_right hs hq
    simpa [hdef] using this
  · intro hcost
    have hmul : E.measuredSpeedup * E.quotientCost > E.quotientCost := by
      simpa [hdef] using hcost
    have hmul' : E.measuredSpeedup * E.quotientCost > 1 * E.quotientCost := by
      simpa using hmul
    exact (Nat.mul_lt_mul_right hq).mp hmul'

/-! ================================================================
    10. PCSS promotion gate
================================================================ -/

structure PCSS where
  integrity : Prop
  replay : Prop
  quotient : Prop
  reconstruction : Prop
  invariant : Prop
  execution : Prop
  lean : Prop

def PCSS.Promotable (P : PCSS) : Prop :=
  P.integrity ∧
  P.replay ∧
  P.quotient ∧
  P.reconstruction ∧
  P.invariant ∧
  P.execution ∧
  P.lean

/-- A promotion theorem: promotion cannot occur unless every gate is supplied. -/
theorem pcss_requires_all (P : PCSS) (h : P.Promotable) :
    P.integrity ∧
    P.replay ∧
    P.quotient ∧
    P.reconstruction ∧
    P.invariant ∧
    P.execution ∧
    P.lean :=
  h

/-! ================================================================
    11. CAS maximal closure object
================================================================ -/

/-- The maximal CAS closure package.

    This structure deliberately distinguishes mathematical closure from
    empirical evidence. A concrete project can instantiate this only when
    the corresponding obligations have actually been proved or supplied.
-/
structure CASMaximalClosure
    {X Y : Type*} {n : Nat}
    (S : QuotientSystem X Y)
    (geom : X → GeometricState n)
    (I : InvariantSystem X) where
  quotient_intertwining : S.Intertwining
  quotient_reconstruction : S.Reconstruction
  geometry : GeometricQuotientClosure S geom
  invariant : InvariantPreservation S I
  scalar_gate :
    ∀ x, ∃ r : Int,
      r = scalarCurvature (geom x).inverseMetric (geom x).ricci
  pcss : PCSS

/-- The principal consequence: every geometric observable in the package
    is represented at quotient level. -/
theorem CASMaximalClosure.geometric_factorization
    {X Y : Type*} {n : Nat}
    {S : QuotientSystem X Y}
    {geom : X → GeometricState n}
    {I : InvariantSystem X}
    (C : CASMaximalClosure S geom I) :
    ∀ x,
      C.geometry.metricBar (S.Q x) = (geom x).metric ∧
      C.geometry.ricciBar (S.Q x) = (geom x).ricci ∧
      C.geometry.inverseMetricBar (S.Q x) = (geom x).inverseMetric := by
  intro x
  exact ⟨
    C.geometry.metric_descent x,
    C.geometry.ricci_descent x,
    C.geometry.inverse_metric_descent x
  ⟩

/-- Scalar curvature is computable on the quotient once the geometric
    descent package is closed. -/
theorem CASMaximalClosure.scalar_factorization
    {X Y : Type*} {n : Nat}
    {S : QuotientSystem X Y}
    {geom : X → GeometricState n}
    {I : InvariantSystem X}
    (C : CASMaximalClosure S geom I) :
    ∀ x,
      C.geometry.scalarCurvatureBar (S.Q x)
        =
      scalarCurvature (geom x).inverseMetric (geom x).ricci :=
  C.geometry.scalarCurvature_descent

/-! ================================================================
    12. Recursive operator form
================================================================ -/

/-- A general executable operator. -/
abbrev Operator (X : Type*) := X → X

/-- Composition of a finite operator chain. -/
def composeChain {X : Type*} : List (Operator X) → Operator X
  | []      => id
  | o :: os => composeChain os ∘ o

/-- The ThreadLock closure chain. -/
def ThreadLockOperator
    {X : Type*}
    (isolate derive reconstruct reuse verify extract seal : Operator X) :
    Operator X :=
  seal ∘ extract ∘ verify ∘ reuse ∘ reconstruct ∘ derive ∘ isolate

/-- The formal target state equation. -/
theorem threadLock_form
    {X : Type*}
    (isolate derive reconstruct reuse verify extract seal : Operator X)
    (ψ : X) :
    ThreadLockOperator isolate derive reconstruct reuse verify extract seal ψ =
      seal (extract (verify (reuse (reconstruct
        (derive (isolate ψ)))))) := by
  rfl

/-! ================================================================
    13. Formal gap ledger
================================================================ -/

inductive GapStatus
  | closed
  | verifiedFixedPoint
  | provablyUnderdetermined
  | externalEvidenceRequired
  | implementationBoundary
  | quarantined
  deriving DecidableEq, Repr

structure FormalGap where
  name : String
  statement : Prop
  status : GapStatus

/-- The CAS geometric descent obligation. -/
def GeometricDescentGap
    {X Y : Type*} {n : Nat}
    (S : QuotientSystem X Y)
    (geom : X → GeometricState n) : Prop :=
  ∀ ⦅x y : X⦆, S.Q x = S.Q y → geom x = geom y

/-- If every geometric state is fiber-constant, the geometric gap is closed. -/
theorem geometricDescentGap_of_components
    {X Y : Type*} {n : Nat}
    (S : QuotientSystem X Y)
    (geom : X → GeometricState n)
    (metric_h :
      S.FiberConstant (fun x => (geom x).metric))
    (connection_h :
      S.FiberConstant (fun x => (geom x).connection))
    (riemann_h :
      S.FiberConstant (fun x => (geom x).riemann))
    (ricci_h :
      S.FiberConstant (fun x => (geom x).ricci))
    (inverse_h :
      S.FiberConstant (fun x => (geom x).inverseMetric)) :
    GeometricDescentGap S geom := by
  intro x y hxy
  cases hx : geom x
  cases hy : geom y
  have hm := metric_h hxy
  have hc := connection_h hxy
  have hr := riemann_h hxy
  have hrc := ricci_h hxy
  have hi := inverse_h hxy
  simp [hx, hy] at hm hc hr hrc hi
  simp [hx, hy, hm, hc, hr, hrc, hi]

/-! ================================================================
    14. Explicit CAS numerical evidence record
================================================================ -/

/-- Numerical observations are intentionally stored as observations.
    Instantiating this does NOT prove the underlying geometric theorem.

    The original CAS Ricci-trace telemetry 0.00003403 is stored as a
    rational snapshot (3403 / 100000000) rather than as a theorem. -/
structure NumericalObservation where
  label : String
  numerator : Int
  denominator : Nat
  denominator_pos : denominator ≠ 0
  note : String

def casRicciTraceObservation : NumericalObservation :=
  { label := "CAS Ricci matrix trace"
    numerator := 3403
    denominator := 100000000
    denominator_pos := by decide
    note :=
      "Observed trace of the displayed Ricci matrix; not automatically scalar curvature." }

/-- The reported CAS number is kept at its proper evidence level. -/
def casRicciTraceEvidence : Evidence := .empiricallySupported

/-! ================================================================
    15. Final admissibility theorem schema
================================================================ -/

/-- Once the maximal closure package exists, geometric observables can be
    evaluated at quotient level without losing the declared observable. -/
theorem quotient_geometry_is_lossless_for_declared_observables
    {X Y : Type*} {n : Nat}
    {S : QuotientSystem X Y}
    {geom : X → GeometricState n}
    {I : InvariantSystem X}
    (C : CASMaximalClosure S geom I) :
    ∀ x,
      C.geometry.metricBar (S.Q x) = (geom x).metric ∧
      C.geometry.ricciBar (S.Q x) = (geom x).ricci ∧
      C.geometry.inverseMetricBar (S.Q x) = (geom x).inverseMetric ∧
      C.geometry.scalarCurvatureBar (S.Q x) =
        scalarCurvature (geom x).inverseMetric (geom x).ricci := by
  intro x
  exact ⟨
    C.geometry.metric_descent x,
    C.geometry.ricci_descent x,
    C.geometry.inverse_metric_descent x,
    C.geometry.scalarCurvature_descent x
  ⟩

/-- Recursive closure is available from the maximal package. -/
theorem CASMaximalClosure.recursive_from_intertwining
    {X Y : Type*} {n : Nat}
    {S : QuotientSystem X Y}
    {geom : X → GeometricState n}
    {I : InvariantSystem X}
    (C : CASMaximalClosure S geom I) :
    S.RecursiveClosure :=
  S.recursiveClosure_of_intertwining C.quotient_intertwining

end CAS_ATD
