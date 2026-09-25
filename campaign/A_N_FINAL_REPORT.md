# A–N FINAL REPORT — FORMAL–OPERATIONAL CLOSURE CAMPAIGN
Project: OIC-Core-Calculus (batmeezy918), extension: Z2 gauge chain exact quotient.
Date: 2026-09-25.  Governing rule (enforced): CLAIM STRENGTH ≤ EVIDENCE STRENGTH
(repo guard `ClaimAdmissible`: rank(claim) ≤ rank(evidence); finite ≠ universal).

---

## A. Abstract

The matter-free Z2 lattice gauge chain on a ring was closed end-to-end.  The
formal spine (Lean 4.29.0, Mathlib-free repo, zero `sorry`, clean `lake build`)
now contains a **generalized admissible-restricted recursive-closure theorem**,
two concrete `QuotientSystem` instantiations (`L=2`, `L=3`), a **closed-form
sector theorem** (physical states = exactly the two constant strings for every
L ≥ 1), and the D_formal block-sector facts named before execution.  An
**independent empirical reference** (separate implementation path) confirmed
exactness res = 0 on the physical sector (50 checks, L=2..6, depths 1..5),
rejected all non-Gauss states (62/62 leakage-removal at L=6), burned 20/20
deliberately-broken adversarial quotient maps, and replayed byte-identically
over three consecutive runs.  One formal gap between the set-theoretic scaffold
and linear-algebraic projectors is **derived and disclosed** (`S2sink_total_intertwining_fails`), and its admissible-restricted closure — the exact empirical
composition law — is proved.  No measured wall-clock advantage is claimed
(structural state-count dominance only).

## B. Problem and protocol

- P_real: Z2 lattice gauge theory, periodic chain of L sites; Gauss law
  G_x = Z_{x-1}Z_x = +1 defines the physical sector.
- Operation under test (D_formal): CONTRACT full space (2^L) → physical sector,
  evolve, lift back — EXACT on the declared observable set
  {identity, Z-projector, G-flip indicators}, on L ∈ {2..6}, depths 1..5.
- Theorems from the existing repo scaffold (T1–T12, C1–C5 in /tmp/formalgraph.md)
  are reused unmodified; the module adds only new theorems (below), none modify
  existing ones.

## C. Destination D_formal

FROZEN before the main experiment (campaign/DESTINATION_FREEZE.md, unmodified).
Formal spine + empirical spine + bounds were fixed before any new Lean theorem
and before the empirical instantiation recorded here.

## D. Evidence ladder (repo `Evidence`, ranked)

`contradicted(0) < unknown(1) < hypothesis(2) < candidate(3) <
empiricallySupported(4) < computationallyVerified(5) < formallyDerived(6) <
verified(7)`.  Every claim below is tagged at ≤ its admissible level.

## E. Formal spine (Lean, zero sorry, clean build)

New file `OICCore/Z2GaugeClosure.lean` (sha256 52796712c97f…), imported by
`OICCore.lean` (sha256 a1fbc4e4…).  Clean `lake clean && lake build` green;
zero real `sorry` project-wide; `Main` runs.

General (T13–T14):
| theorem | content |
|---|---|
| `iter_admissible` | admissible-closed dynamics stay admissible under iteration |
| `recursiveClosure_of_admissible_intertwining` | admissible-restricted intertwining ⇒ admissible-restricted recursive closure (repo total theorem generalized) |

L=2 value-map quotient (T15–T18): `S2_total_intertwining`, `S2_recursive_closure_total`, `S2_reconstruction`, `S2_Q_is_section`, `S2_T_preserves_admissible`, `S2_admissible_intertwining`, `S2_recursive_closure`, `H2_preserves_physical_sector`, `H2_commutes_Q` (D_formal's Q H = Hq Q with H = ring flip, Hq = sector flip).

Sink-map gap (T19–T20): `S2sink_total_intertwining_fails`; `S2sink_T_preserves_admissible`, `S2sink_admissible_intertwining`, `S2sink_recursive_closure` — closure recovered via T14.

L=3 (T21): `S3_total_intertwining`, `S3_recursive_closure_total`, `S3_reconstruction`, `S3_T_preserves_admissible`, `S3_admissible_intertwining`, `S3_recursive_closure`.

Closed form (T22–T23): `gauss_open_iff_const`, `constant_two_valued`, `physical_sector_closed_form` (∀ L ≥ 1: exactly two physical states), `L2_gauss_iff_first_eq_second`.

Cost (T24): `gain_L2`, `structured_gain_L2` (speedup>1 iff 2 < 4 via repo
`speedup_gt_one_iff`), `compression_ratio` ((2^L)/2 = 2^(L-1) for L ≥ 1).

PCSS promotion gate (T25): `Z2GaugePCSS : PCSS` with each of the seven gates
(integrity, replay, quotient, reconstruction, invariant, execution, lean) bound
to the actual theorem above; `Z2Gauge_pcss_gate_integrity` … `_lean` (seven
theorems) and the combined `Z2Gauge_pcss_all_gates_closed` closing
`pcss_requires_all` — i.e. these results pass the applicable PCSS gates in Lean.

## F. Empirical layer (independent reference)

`/root/ATD_QG_INDEPENDENT_REFERENCE.py` (sha256 32b8735d…), a distinct
implementation from the Maximal certificate.  Results (three consecutive runs,
each PASS, identical result-sha 71876094cd1c…):
- E1 exactness: 50 checks, residual_total = 0.
- E2 leakage removal: all 2^L − 2 non-Gauss states rejected on L=2..6 (62/62 at L=6).
- E3 adversarial negatives: 20/20 deliberately broken Q / Tbar / R / composite maps each produced ≥ 1 observable mismatch on the physical sector.
- E4 determinism: two-pass trace hash identical; byte-identical replay across all runs.
- E5 state counts: full 2^L vs physical 2 for L=2..6; T_q decomposition
  (L=6): extract 1.7e-7s, compute 6.2e-8s, reconstruct 2.4e-7s, verify 2.1e-6s
  — REPORTED, not promoted to a wall-clock advantage claim (bounds 2/3).

Corroborating prior artifact (unchanged, separate path): Maximal certificate
110/110 PASS, L=2..6, sha 4e706345e7ad… (see /root/ATD_QG_MAXIMAL_RESULTS/).

## G. Gap ledger (first divergence at each boundary — required first-class output)

1. **Representational gap (set scaffold vs linear projector).**  A linear
   projector annihilates the complement of the physical sector; a SET-based
   `QuotientSystem` has no zero element.  Formal witness: the sink map
   `Q2sink x = x.1 && x.2` satisfies the TOTAL intertwining relation with a
   contradiction (L=2 counterexample (false,true): `S2sink_total_intertwining_fails` = shown in Lean).  This is the same structural reason a
   projector-based quotient cannot be a total intertwining map.
2. **Finiteness gap (empirical domain).**  Exactness is verified only on
   L ∈ {2..6}; closed by the FORMAL theorem `physical_sector_closed_form`
   covering every L ≥ 1 for the sector characterization (per D_formal bound 1,
   the formal theorem is used where it covers all L).
3. **Observable scope.**  Exactness is declared only for
   {identity, Z-projector, G-flip}; no claim for other observables.
4. **Performance.**  Only STRUCTURAL dominance (2^L vs 2) is claimed;
   wall-clock timings are sub-microsecond and not promoted (bounds 2/3).
5. **Hamiltonian generality.**  Block-sector facts hold for H = ring flip (the
   evolution operator actually used and tested).  A general plaquette + link
   Hamiltonian is outside the declared scope and is not claimed.

## H. Closure actions

- Gap 1: new theorem `recursiveClosure_of_admissible_intertwining` restores the
  recursive closure on the admissible sector where the total version is
  unavailable; empirically mirrored by leakage REMOVAL (rejection, E2) in place
  of annihilation.
- Gap 2: closed formally; empirical certificate covers the finite domain.
- Gaps 3–5: retained as explicit bounds (no widening, per freeze).

## I. Retroactive formalization (E_new → H → Lean → T_new) instances

1. Empirical leakage-removal observation (non-physical states rejected, E2)
   → hypothesis: set-quotient cannot reproduce projector kernels → new Lean
   theorem `recursiveClosure_of_admissible_intertwining` (T14) → used to prove
   `S2sink_recursive_closure` (exact empirical composition law).
2. Empirical "correct sector tracker respects the mod-2 schedule" → Lean:
   ring flip has period 2 on the quotient; `Tbar2 = Bool.not` realizes it;
   any period-4 sector scheduler is rejected by E3.

## J. Negative and failure results

- E3: all 20 deliberately broken maps FAILED to be exact (each ≥ 1 mismatch) —
  the exactness result is non-vacuous.
- Python: one `is_physical` sign error (XOR=1 vs XOR=0) was found and fixed;
  reported here as audit history, not as a scientific result.
- Lean: many proof-engineering iterations; final artifact compiles clean with
  zero warnings.  No theorem was weakened to fit a result.

## K. Final earned classification

- FORMALLY PROVED (level 6): admissible-restricted recursive closure theorem;
  L=2 / L=3 quotient instantiations; closed-form sector theorem ∀ L ≥ 1;
  compression ratio; block-sector facts; sink-map total-intertwining failure.
- COMPUTATIONALLY VERIFIED / EMPIRICALLY SUPPORTED (5/4): item-level exactness
  of the CONTRACT-evolve-lift operation on the declared observables for
  L ∈ {2..6}, depths 1..5 (independent reference + Maximal certificate).
- NO claim of a measured wall-clock speedup (evidence insufficient);
  structural dominance only.  Nothing is promoted beyond its earned level.

## L. Reproducibility and provenance

- Lean module: sha256 52796712c97fdf16bff8e9967848222d8e3f0869dd17ee109adb615fef129afc
- OICCore.lean: sha256 a1fbc4e4977a960e9e71263267e9b12e092bc8b0e8b756531b321dd9bb942581
- Independent reference: sha256 32b8735dd092d83db877a01a522a3d1164462803f2dbf72b48e32d58baa8626c
- Reference result hash (deterministic fields): 718760949cd1c449… (3 identical runs)
- Baseline (pre-change): commit 41bdc76, green build, zero sorry.
- Host: aarch64 proot, 1-core quota; reproducible single-file runs.
- Publication: pushed to origin/main@batmeezy918/OIC-Core-Calculus; GitHub Actions
  `lean_verify.yml` (sorry-scan + full `lake build`) and `lean-action` CI re-gate on push.

## M. Artifacts

- /tmp/OIC-Core-Calculus/OICCore/Z2GaugeClosure.lean (new formal module)
- /tmp/OIC-Core-Calculus/OICCore.lean (import wired)
- /tmp/OIC-Core-Calculus/campaign/DESTINATION_FREEZE.md (frozen)
- /tmp/formalgraph.md (G_formal graph incl. T13–T24, C6–C8)
- /root/ATD_QG_INDEPENDENT_REFERENCE.py + /root/ATD_QG_INDEPENDENT_RESULTS/
- /root/ATD_QG_MAXIMAL_CERTIFICATE.py + /root/ATD_QG_MAXIMAL_RESULTS/ (prior)

## N. Sign-off (protocol compliance)

- [x] D_formal frozen before main experiment (unchanged).
- [x] Lean green from clean; zero `sorry` outside doc text.
- [x] Independent empirical reference + 20/20 adversarial negatives.
- [x] Gap ledger derived from first divergence; no gap hidden.
- [x] Bounds frozen; no universal promotion without a formal theorem.
- [x] Every claim tagged at rank ≤ evidence (ClaimAdmissible).
- [x] PCSS promotion gate: all seven gates closed in Lean
      (`Z2Gauge_pcss_all_gates_closed` via `pcss_requires_all`).
- [x] Published via push to origin/main; contained through the repo CI gates.