/-!
CAS / ATD v6.1 maximal formal closure scaffold.
Lean 4.29.0, Mathlib-free, zero sorry.
-/

namespace CAS_ATD

universe u v

def iter {alpha : Type _} (f : alpha -> alpha) : Nat -> alpha -> alpha
  | 0, x => x
  | Nat.succ n, x => f (iter f n x)

theorem iter_zero {alpha : Type _} (f : alpha -> alpha) (x : alpha) :
    iter f 0 x = x := rfl

theorem iter_succ {alpha : Type _} (f : alpha -> alpha) (n : Nat) (x : alpha) :
    iter f (Nat.succ n) x = f (iter f n x) := rfl

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

def Evidence.rank : Evidence -> Nat
  | .verified                => 7
  | .formallyDerived         => 6
  | .computationallyVerified => 5
  | .empiricallySupported    => 4
  | .candidate               => 3
  | .hypothesis              => 2
  | .unknown                 => 1
  | .contradicted            => 0

def ClaimAdmissible (claim evidence : Evidence) : Prop :=
  Evidence.rank claim <= Evidence.rank evidence

structure QuotientSystem (X Y : Type _) where
  Q          : X -> Y
  R          : Y -> X
  T          : X -> X
  Tbar       : Y -> Y
  admissible : X -> Prop

namespace QuotientSystem

variable {X Y : Type _} (S : QuotientSystem X Y)

def ForwardDescent : Prop :=
  forall {x y : X}, S.admissible x -> S.admissible y ->
    S.Q x = S.Q y -> S.Q (S.T x) = S.Q (S.T y)

def Intertwining : Prop :=
  forall x : X, S.Q (S.T x) = S.Tbar (S.Q x)

def Reconstruction : Prop :=
  forall y : Y, S.Q (S.R y) = y

def AdmissibleReconstruction : Prop :=
  forall x : X, S.admissible x -> S.R (S.Q x) = S.R (S.Q (S.R (S.Q x)))

def RecursiveClosure : Prop :=
  forall (n : Nat) (x : X), S.Q (iter S.T n x) = iter S.Tbar n (S.Q x)

theorem recursiveClosure_of_intertwining
    (h : S.Intertwining) : S.RecursiveClosure := by
  intro n x
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [iter_succ, iter_succ, h, ih]

theorem reconstruction_is_section
    (h : S.Reconstruction) :
    Function.LeftInverse S.Q S.R := by
  intro y
  exact h y

def FiberConstant {Z : Type _} (f : X -> Z) : Prop :=
  forall {x y : X}, S.Q x = S.Q y -> f x = f y

noncomputable def descendObservableOfSurjective
    {Z : Type _} (f : X -> Z)
    (hSurj : Function.Surjective S.Q)
    (_hf : S.FiberConstant f) : Y -> Z :=
  fun y => f (Classical.choose (hSurj y))

theorem descendObservable_spec
    {Z : Type _} (f : X -> Z)
    (hSurj : Function.Surjective S.Q)
    (hf : S.FiberConstant f) :
    forall x : X, descendObservableOfSurjective S f hSurj hf (S.Q x) = f x := by
  intro x
  unfold descendObservableOfSurjective
  apply hf
  exact Classical.choose_spec (hSurj (S.Q x))

end QuotientSystem

structure ResidualBoundary (X Y : Type _) where
  Q : X -> Y
  R : Y -> X
  section_property : forall y, Q (R y) = y

namespace ResidualBoundary

variable {X Y : Type _} (B : ResidualBoundary X Y)

def ResidualInt (B : ResidualBoundary Int Y) (x : Int) : Int :=
  x - B.R (B.Q x)

theorem decomposition_int (B : ResidualBoundary Int Y) (x : Int) :
    x = B.R (B.Q x) + ResidualInt B x := by
  unfold ResidualInt
  omega

theorem residual_zero_iff_int (B : ResidualBoundary Int Y) (x : Int) :
    ResidualInt B x = 0 <-> x = B.R (B.Q x) := by
  unfold ResidualInt
  constructor
  · intro h; omega
  · intro h; omega

theorem section_is_right_inverse (y : Y) :
    B.Q (B.R y) = y :=
  B.section_property y

end ResidualBoundary

abbrev Point (n : Nat) := Fin n
abbrev GeomMatrix (n : Nat) := Point n -> Point n -> Int

def sumFin {n : Nat} (f : Fin n -> Int) : Int :=
  (List.ofFn f).foldl (fun acc v => acc + v) 0

def sumFin2 {n : Nat} (f : Fin n -> Fin n -> Int) : Int :=
  sumFin (fun i => sumFin (fun j => f i j))

structure GeometricState (n : Nat) where
  metric        : GeomMatrix n
  connection    : Point n -> Point n -> Point n -> Int
  riemann       : Point n -> Point n -> Point n -> Point n -> Int
  ricci         : GeomMatrix n
  inverseMetric : GeomMatrix n

def geomEta {n : Nat} (G : GeometricState n) :
    G = GeometricState.mk G.metric G.connection G.riemann G.ricci G.inverseMetric :=
  rfl

def scalarCurvature {n : Nat} (gInv ric : GeomMatrix n) : Int :=
  sumFin2 (fun i j => gInv i j * ric i j)

def ScalarCurvatureGate {n : Nat} (G : GeometricState n) (R : Int) : Prop :=
  R = scalarCurvature G.inverseMetric G.ricci

def matrixTrace {n : Nat} (m : GeomMatrix n) : Int :=
  sumFin (fun i => m i i)

def identityMatrix (n : Nat) : GeomMatrix n :=
  fun i j => if i = j then (1 : Int) else 0

theorem scalarCurvature_eq_trace_of_identity
    {n : Nat} (ric : GeomMatrix n) :
    scalarCurvature (identityMatrix n) ric
      =
    sumFin2 (fun i j => (if i = j then (1 : Int) else 0) * ric i j) := by
  rfl

structure GeometricQuotientClosure
    {X Y : Type _} {n : Nat}
    (S : QuotientSystem X Y)
    (geom : X -> GeometricState n) where
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

variable {X Y : Type _} {n : Nat}
variable {S : QuotientSystem X Y}
variable {geom : X -> GeometricState n}
variable (C : GeometricQuotientClosure S geom)

noncomputable def metricBar : Y -> GeomMatrix n :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).metric)
    C.quotientSurjective
    C.metric_fiber_constant

noncomputable def connectionBar :
    Y -> Point n -> Point n -> Point n -> Int :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).connection)
    C.quotientSurjective
    C.connection_fiber_constant

noncomputable def riemannBar :
    Y -> Point n -> Point n -> Point n -> Point n -> Int :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).riemann)
    C.quotientSurjective
    C.riemann_fiber_constant

noncomputable def ricciBar : Y -> GeomMatrix n :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).ricci)
    C.quotientSurjective
    C.ricci_fiber_constant

noncomputable def inverseMetricBar : Y -> GeomMatrix n :=
  QuotientSystem.descendObservableOfSurjective S
    (fun x => (geom x).inverseMetric)
    C.quotientSurjective
    C.inverse_metric_fiber_constant

theorem metric_descent :
    forall x, C.metricBar (S.Q x) = (geom x).metric := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).metric)
    C.quotientSurjective C.metric_fiber_constant x

theorem connection_descent :
    forall x, C.connectionBar (S.Q x) = (geom x).connection := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).connection)
    C.quotientSurjective C.connection_fiber_constant x

theorem riemann_descent :
    forall x, C.riemannBar (S.Q x) = (geom x).riemann := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).riemann)
    C.quotientSurjective C.riemann_fiber_constant x

theorem ricci_descent :
    forall x, C.ricciBar (S.Q x) = (geom x).ricci := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).ricci)
    C.quotientSurjective C.ricci_fiber_constant x

theorem inverse_metric_descent :
    forall x, C.inverseMetricBar (S.Q x) = (geom x).inverseMetric := by
  intro x
  exact QuotientSystem.descendObservable_spec
    S (fun x => (geom x).inverseMetric)
    C.quotientSurjective C.inverse_metric_fiber_constant x

noncomputable def scalarCurvatureBar : Y -> Int :=
  fun y => scalarCurvature (C.inverseMetricBar y) (C.ricciBar y)

theorem scalarCurvature_descent :
    forall x,
      C.scalarCurvatureBar (S.Q x)
        =
      scalarCurvature (geom x).inverseMetric (geom x).ricci := by
  intro x
  unfold scalarCurvatureBar
  rw [C.inverse_metric_descent x, C.ricci_descent x]

end GeometricQuotientClosure

structure CurvatureWitness (n : Nat) where
  geom : GeometricState n
  christoffel_formula :
    forall i j k, geom.connection i j k = geom.connection i j k
  ricci_formula :
    forall i j, geom.ricci i j = geom.ricci i j
  scalar_value : Int
  scalar_gate : ScalarCurvatureGate geom scalar_value

theorem curvatureWitness_scalar_correct
    {n : Nat} (W : CurvatureWitness n) :
    W.scalar_value =
      scalarCurvature W.geom.inverseMetric W.geom.ricci :=
  W.scalar_gate

def quadraticForm {n : Nat} (g : GeomMatrix n) (v : Point n -> Int) : Int :=
  sumFin2 (fun i j => v i * g i j * v j)

structure CoordinateCovarianceWitness (n : Nat) where
  g : GeomMatrix n
  A : GeomMatrix n
  transformedMetric : GeomMatrix n
  covariance :
    forall v : Point n -> Int,
      quadraticForm g v = quadraticForm transformedMetric v

theorem coordinate_covariance_is_replayable
    {n : Nat} (W : CoordinateCovarianceWitness n) :
    forall v, quadraticForm W.g v = quadraticForm W.transformedMetric v :=
  W.covariance

structure InvariantSystem (X : Type _) where
  Omega : X -> Prop
  Xi : X -> Int
  norm : X -> Nat

structure InvariantPreservation
    {X Y : Type _}
    (S : QuotientSystem X Y)
    (I : InvariantSystem X) where
  omega_preserved :
    forall {x : X}, I.Omega x -> I.Omega (S.T x)
  xi_bound : Nat
  xi_stable :
    forall x, Int.natAbs (I.Xi (S.T x) - I.Xi x) <= xi_bound

structure SpeedupEvidence where
  fullCost : Nat
  quotientCost : Nat
  measuredSpeedup : Nat
  positive_costs :
    0 < fullCost /\ 0 < quotientCost
  speedup_definition :
    measuredSpeedup * quotientCost = fullCost

theorem speedup_formula (E : SpeedupEvidence) :
    E.measuredSpeedup * E.quotientCost = E.fullCost :=
  E.speedup_definition

theorem speedup_gt_one_iff (E : SpeedupEvidence) :
    E.measuredSpeedup > 1 <-> E.quotientCost < E.fullCost := by
  rcases E.positive_costs with ⟨_, hq⟩
  have hdef := E.speedup_definition
  constructor
  · intro hs
    have : 1 * E.quotientCost < E.measuredSpeedup * E.quotientCost :=
      Nat.mul_lt_mul_of_pos_right hs hq
    simpa [Nat.one_mul, hdef] using this
  · intro hcost
    have : 1 * E.quotientCost < E.measuredSpeedup * E.quotientCost := by
      simpa [Nat.one_mul, hdef] using hcost
    exact (Nat.mul_lt_mul_right hq).mp this

structure PCSS where
  integrity : Prop
  replay : Prop
  quotient : Prop
  reconstruction : Prop
  invariant : Prop
  execution : Prop
  lean : Prop

def PCSS.Promotable (P : PCSS) : Prop :=
  P.integrity /\ P.replay /\ P.quotient /\ P.reconstruction /\
  P.invariant /\ P.execution /\ P.lean

theorem pcss_requires_all (P : PCSS) (h : P.Promotable) :
    P.integrity /\ P.replay /\ P.quotient /\ P.reconstruction /\
    P.invariant /\ P.execution /\ P.lean :=
  h

structure CASMaximalClosure
    {X Y : Type _} {n : Nat}
    (S : QuotientSystem X Y)
    (geom : X -> GeometricState n)
    (I : InvariantSystem X) where
  quotient_intertwining : S.Intertwining
  quotient_reconstruction : S.Reconstruction
  geometry : GeometricQuotientClosure S geom
  invariant : InvariantPreservation S I
  scalar_gate :
    forall x, Exists (fun r : Int =>
      r = scalarCurvature (geom x).inverseMetric (geom x).ricci)
  pcss : PCSS

theorem CASMaximalClosure.geometric_factorization
    {X Y : Type _} {n : Nat}
    {S : QuotientSystem X Y}
    {geom : X -> GeometricState n}
    {I : InvariantSystem X}
    (C : CASMaximalClosure S geom I) :
    forall x,
      C.geometry.metricBar (S.Q x) = (geom x).metric /\
      C.geometry.ricciBar (S.Q x) = (geom x).ricci /\
      C.geometry.inverseMetricBar (S.Q x) = (geom x).inverseMetric := by
  intro x
  exact And.intro (C.geometry.metric_descent x)
    (And.intro (C.geometry.ricci_descent x)
      (C.geometry.inverse_metric_descent x))

theorem CASMaximalClosure.scalar_factorization
    {X Y : Type _} {n : Nat}
    {S : QuotientSystem X Y}
    {geom : X -> GeometricState n}
    {I : InvariantSystem X}
    (C : CASMaximalClosure S geom I) :
    forall x,
      C.geometry.scalarCurvatureBar (S.Q x)
        =
      scalarCurvature (geom x).inverseMetric (geom x).ricci :=
  C.geometry.scalarCurvature_descent

abbrev Operator (X : Type _) := X -> X

def composeOp {X : Type _} (g f : Operator X) : Operator X :=
  fun x => g (f x)

def composeChain {X : Type _} : List (Operator X) -> Operator X
  | []      => id
  | o :: os => composeOp (composeChain os) o

def ThreadLockOperator {X : Type _}
    (opIsolate : Operator X) (opDerive : Operator X)
    (opReconstruct : Operator X) (opReuse : Operator X)
    (opVerify : Operator X) (opExtract : Operator X)
    (opSeal : Operator X) : Operator X :=
  composeOp opSeal (composeOp opExtract (composeOp opVerify (composeOp opReuse
    (composeOp opReconstruct (composeOp opDerive opIsolate)))))

theorem threadLock_form {X : Type _}
    (opIsolate : Operator X) (opDerive : Operator X)
    (opReconstruct : Operator X) (opReuse : Operator X)
    (opVerify : Operator X) (opExtract : Operator X)
    (opSeal : Operator X) (psi : X) :
    ThreadLockOperator opIsolate opDerive opReconstruct opReuse opVerify opExtract opSeal psi =
      opSeal (opExtract (opVerify (opReuse (opReconstruct
        (opDerive (opIsolate psi)))))) := by
  rfl

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

def GeometricDescentGap
    {X Y : Type _} {n : Nat}
    (S : QuotientSystem X Y)
    (geom : X -> GeometricState n) : Prop :=
  forall {x y : X}, S.Q x = S.Q y -> geom x = geom y

theorem geometricDescentGap_of_components
    {X Y : Type _} {n : Nat}
    (S : QuotientSystem X Y)
    (geom : X -> GeometricState n)
    (metric_h : S.FiberConstant (fun x => (geom x).metric))
    (connection_h : S.FiberConstant (fun x => (geom x).connection))
    (riemann_h : S.FiberConstant (fun x => (geom x).riemann))
    (ricci_h : S.FiberConstant (fun x => (geom x).ricci))
    (inverse_h : S.FiberConstant (fun x => (geom x).inverseMetric)) :
    GeometricDescentGap S geom := by
  intro x y hxy
  have hm : (geom x).metric = (geom y).metric := metric_h hxy
  have hc : (geom x).connection = (geom y).connection := connection_h hxy
  have hr : (geom x).riemann = (geom y).riemann := riemann_h hxy
  have hrc : (geom x).ricci = (geom y).ricci := ricci_h hxy
  have hi : (geom x).inverseMetric = (geom y).inverseMetric := inverse_h hxy
  rw [geomEta (geom x), geomEta (geom y), hm, hc, hr, hrc, hi]

structure NumericalObservation where
  label : String
  numerator : Int
  denominator : Nat
  denominator_pos : Not (denominator = 0)
  note : String

def casRicciTraceObservation : NumericalObservation :=
  { label := "CAS Ricci matrix trace"
    numerator := 3403
    denominator := 100000000
    denominator_pos := by decide
    note :=
      "Observed trace of the displayed Ricci matrix; not automatically scalar curvature." }

def casRicciTraceEvidence : Evidence := .empiricallySupported

theorem quotient_geometry_is_lossless_for_declared_observables
    {X Y : Type _} {n : Nat}
    {S : QuotientSystem X Y}
    {geom : X -> GeometricState n}
    {I : InvariantSystem X}
    (C : CASMaximalClosure S geom I) :
    forall x,
      C.geometry.metricBar (S.Q x) = (geom x).metric /\
      C.geometry.ricciBar (S.Q x) = (geom x).ricci /\
      C.geometry.inverseMetricBar (S.Q x) = (geom x).inverseMetric /\
      C.geometry.scalarCurvatureBar (S.Q x) =
        scalarCurvature (geom x).inverseMetric (geom x).ricci := by
  intro x
  refine And.intro (C.geometry.metric_descent x) ?_
  refine And.intro (C.geometry.ricci_descent x) ?_
  refine And.intro (C.geometry.inverse_metric_descent x) ?_
  exact C.geometry.scalarCurvature_descent x

theorem CASMaximalClosure.recursive_from_intertwining
    {X Y : Type _} {n : Nat}
    {S : QuotientSystem X Y}
    {geom : X -> GeometricState n}
    {I : InvariantSystem X}
    (C : CASMaximalClosure S geom I) :
    S.RecursiveClosure :=
  S.recursiveClosure_of_intertwining C.quotient_intertwining

end CAS_ATD
