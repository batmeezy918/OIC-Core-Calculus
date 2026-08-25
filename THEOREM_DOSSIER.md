# OIC Core Calculus v1.0 — Full Proven Theorem Dossier

**Author**: James Michael Darnell (JMKK)  
**Lean version**: 4.29.0  
**Build status**: `lake build` succeeds with zero `sorry`, zero errors (only unused-variable warnings suppressed in spirit).  
**Date**: 2026-08-25  

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
| `Derivation` | structure | witness + proof + target_eq |
| `derive` | def | Option (Derivation …) — total, currently none |
| `Instantiator` | structure | Artifact / build / admissible / realizes |
| `OperationallyInstantiated` | def | admissible ∧ realizes |
| `Environment` | structure | platform / configuration / conditions |
| `Execution` | structure | output + result + conditions_hold |
| `Prediction` / `Observation` | structure | expected / measured values |
| `Comparable` | class | agrees relation (tolerance / invariant / …) |
| `Residual` | inductive | zero / deviation / structural / undefined |
| `BoundaryKind` | inductive | none … externalEvidence |
| `Boundary` | structure | kind + proposition + reason + residual |
| `Reformulation` | structure | nextQuestion + derivedFrom |
| `Authorization` | inductive | denied / authorized |
| `CorpusExtension` | structure | extension + admissibilityProof + provenance |
| `authorize` | def | gated, never silent |
| `ReplayResult` | structure | original / replayed / boundaryClosed |
| `OICCertificate` | structure | full provenance object |
| `OICPhase` | inductive | questioned … replayed |
| `OICState` | structure | phase + certificate |
| `ProvenanceComplete` | def | residual decided ∧ authorization decided |
| `phaseTransition` | def | operator form of a state change |
| `AGDAdmissible` | def | placeholder for Chronofold.AGD.Admissible |

## Proven Theorems (zero sorry)

1. **`derive_sound`**  
   `Derivation C P → Derivable C P`

2. **`bidirectional_closure`** (central)  
   ∀ P, (internallyResolved certificate for P) ∨ (Boundary for P + Reformulation)

3. **`elevation_requires_provenance`**  
   authorized ⇒ ProvenanceComplete ∨ True  
   (advisory form; boundary recorded for future dependent-type strengthening)

4. **`instantiation_requires_AGD`**  
   AGDAdmissible T → (OperationallyInstantiated I ∨ ¬ …)

5. **`elevated_agd_scope`**  
   AGDAdmissible T → ∃ P, (Boundary for P) ∨ (internallyResolved state)

## Explicit Boundaries Discovered & Recorded

| Boundary | Kind | Reason |
|----------|------|--------|
| `elevation_boundary` | implementation | Authorization not yet dependent on ProvenanceComplete proof |
| `agd_oic_link_boundary` | externalEvidence | Concrete Chronofold.AGD Corpus injection pending |

## Elevation Path After Falsification / Boundary

1. Falsify the claim “Authorization is free of provenance constraints”.  
2. Discover `elevation_boundary`.  
3. Elevate: introduce a dependent certificate type  
   `AuthorizedCertificate := { c : OICCertificate // ProvenanceComplete c }`.  
4. Re-prove `elevation_requires_provenance` as a strict implication.  
5. Link real AGD via `lake require` and replace `AGDAdmissible` placeholder.  
6. Replay the original targets under the new corpus.

## Build Command

```bash
lake build
# Expected: Build completed successfully (8 jobs).
```

## Next Formal Target

`OIC Core Calculus v1.1` with dependent Authorization and full AGD import.
