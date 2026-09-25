# FROZEN DESTINATION — recorded before main experiment execution

Locked at: campaign start (after G_formal synthesis). Recorded before any new Lean theorem and
before the main empirical instantiation.

## D_formal (unchanged from this point)
For the real quantum problem P_real = "matter-free Z_2 lattice gauge theory on a
periodic chain, L sites, Gauss law G_x = Z_{x-1} Z_x = +1 (physical sector)", the
operation

    CONTRACT: full state space (2^L) -> physical sector (2^(L-1)), evolve, lift back

is EXACT (zero-residual) on the declared observable set, and the time/space cost of
the contracted program is strictly less than the full program on the tested finite
instances L = 2..6. The claim is made with strength graded by evidence:

  * Formal (Lean 4.29.0, Mathlib-free repo, zero sorry): 
      - admissible-restricted intertwining implies admissible-restricted recursive
        closure (new theorem, generalizes repo recursiveClosure_of_intertwining);
      - concrete instances L=2 and L=3 instantiating QuotientSystem with the Z2 gauge
        quotient, Q=physical growth map, T=ring flip, Tbar=sector flip, admitting
        Intertwining + reconstruction + recursive closure on the admissible sector;
      - block-sector facts for the L=2 gauge Hamiltonian (H preserves physical sector;
        Q H = Hq Q; speedup-threshold decidable by the repo's speedup_gt_one_iff).
  * Empirical (independent full-vs-quotient reference, numpy, deterministic replay):
      - identical states/observables, zero residual on physical sector, leakage removed,
        20/20 adversarial negatives rejected, composition depth 1..5 (L=2..6),
        timing decomposition T_q = extract + compute + reconstruct + verify,
        end-to-end total and kernel-level report, determinism byte-identical replay.

## Claim bounds (frozen, will not be widened)
1. "Exactness" is declared on the finite tested domain L in {2,3,4,5,6} and on the
   declared observable set {identity, Z-projector, G-flip indicators} unless a formal
   theorem covers all L (if the sector-dimension theorem is completed for general L it
   is used, but no universal metric/spectral claim is promoted from finite runs).
2. No time/space advantage claim is made at L where the quotient is not smaller.
3. Results are classified at their earned evidence level; nothing is labeled
   FORMALLY PROVED unless it is in Lean with zero sorry and a green lake build.