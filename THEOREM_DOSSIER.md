# OIC Core Calculus v1.1 — Full Proven Theorem Dossier

**Author**: James Michael Darnell (JMKK)  
**Lean version**: 4.29.0  
**Build status**: `lake build` succeeds with **zero `sorry`**, zero errors.  
**Date**: 2026-08-25  
**Elevation**: v1.0 → v1.1 after falsification of free authorization & empty-corpus derivability.

## Dependency Architecture

```
AGD Corpus (Chronofold.AGD.*)  →  OIC Core  →  ThreadLock-RCC  →  Reality-Coherence
```

No backward contamination. AGD theorems remain external substrate.

## Constitutional Core (Structures & Definitions)

| Symbol | Kind | Description |
|--------|------|-------------|
| `Proposition` | abbrev | `Prop` |
| `Corpus` | structure | Name + theoremRef |
| `Derivable` | def | ∃ witness matching P |
| `ProofState` | structure | Carrier for operator algebra |
| `Operator` | abbrev | ProofState → ProofState |
| `Compose` / `∘ₒ` | def | Operator composition |
| `IdOp` | def | Identity operator |
| `Derivation` | structure | witness + proof + target_eq |
| `derive` | def | Option (Derivation …) — total, currently none |
| `Instantiator` | structure | Artifact / build / admissible / realizes |
| `OperationallyInstantiated` | def | admissible ∧ realizes |
| `Environment` | structure | platform / configuration / conditions |
| `Execution` | structure | output + result + conditions_hold |
| `Prediction` / `Observation` | structure | expected / measured values |
| `Comparable` | class | agrees relation (tolerance / invariant / …) |
| `Residual` | inductive | zero / deviation / structural / undefined |
| `Residual.isDecided` / `isZero` | def | Decision predicates |
| `BoundaryKind` | inductive | none … externalEvidence |
| `Boundary` | structure | kind + proposition + reason + residual |
| `Reformulation` | structure | nextQuestion + derivedFrom |
| `Authorization` | inductive | denied / authorized |
| `CorpusExtension` | structure | extension + admissibilityProof + provenance |
| `authorize` | def | gated, never silent |
| `ReplayResult` | structure | original / replayed / boundaryClosed |
| `OICCertificate` | structure | full provenance object |
| `AuthorizedCertificate` | structure | dependent subtype (complete + authorized) |
| `OICPhase` | inductive | questioned … replayed |
| `OICState` | structure | phase + certificate |
| `ProvenanceComplete` | def | residual decided ∧ authorization decided |
| `phaseTransition` | def | operator form of a state change |
| `ThreadLockOutput` | inductive | certified / empiricallyInstantiated / boundary / externalRequisition |
| `RealityCoherenceResult` | inductive | coherent / residualBoundary / … |
| `OperationallyRealized` | def | residual zero ∨ decided |
| `AGDAdmissible` | def | placeholder for Chronofold.AGD.Admissible |

## Proven Theorems (zero sorry)

1. **`Compose_assoc`**  
   `Compose (Compose O₃ O₂) O₁ = Compose O₃ (Compose O₂ O₁)`

2. **`IdOp_left` / `IdOp_right`**  
   Identity is left and right unit for composition.

3. **`derive_sound`**  
   `Derivation C P → Derivable C P`

4. **`residual_zero_is_decided`**  
   `Residual.zero.isDecided`

5. **`bidirectional_closure`** (central)  
   ∀ P, (internallyResolved certificate for P) ∨ (Boundary for P + Reformulation)

6. **`empty_corpus_always_boundary`** (maximized diagnostic)  
   `derive C P = none ∧ ∃ B, B.proposition = P ∧ (B.kind = derivation ∨ definition)`

7. **`phaseTransition_preserves_cert`**  
   Phase change never mutates the certificate.

8. **`elevation_requires_provenance`** (elevated)  
   authorization ⇒ ProvenanceComplete ∨ explicit implementation Boundary

9. **`authorized_implies_provenance`**  
   `AuthorizedCertificate → ProvenanceComplete`

10. **`rcc_coherent_implies_realized`**  
    residual.isZero → OperationallyRealized (domain-scoped)

11. **`residual_zero_sound`**  
    residual = zero ∧ auth decided → ProvenanceComplete

12. **`instantiation_requires_AGD`**  
    AGDAdmissible T → (OperationallyInstantiated I ∨ ¬ …)

13. **`elevated_agd_scope`**  
    AGDAdmissible T → ∃ P, (Boundary for P) ∨ (internallyResolved state)

14. **`authorized_extension_replay`**  
    authorized + authorize = none → explicit implementation Boundary

15. **`can_detect_boundary`**  
    Every certificate can enter boundaryDetected phase preserving question.

## Explicit Boundaries Discovered & Recorded

| Boundary | Kind | Reason |
|----------|------|--------|
| `elevation_boundary` | implementation | Authorization not yet dependent on ProvenanceComplete proof |
| `agd_oic_link_boundary` | externalEvidence | Concrete Chronofold.AGD Corpus injection pending |
| (from empty_corpus) | derivation | derive always returns none under current Corpus |

## Elevation Path After Falsification / Boundary

1. Falsify “Authorization is free of provenance constraints”.  
2. Discover `elevation_boundary`.  
3. Elevate: introduce dependent `AuthorizedCertificate`.  
4. Re-prove elevation as disjunction with explicit Boundary emission.  
5. Maximize under empty corpus: `empty_corpus_always_boundary`.  
6. Add ThreadLock four-class taxonomy + RCC domain-scoped soundness.  
7. Next: materialize real AGD via `lake require` and replace placeholders; make `authorize` return a concrete extended Corpus under authorized.

## Build Command

```bash
lake build
# Expected: Build completed successfully (8 jobs).
```

## Next Formal Target

`OIC Core Calculus v1.2` with concrete AGD Corpus injection and non-trivial `derive` / `authorize` implementations that still preserve totality and zero-sorry discipline.
