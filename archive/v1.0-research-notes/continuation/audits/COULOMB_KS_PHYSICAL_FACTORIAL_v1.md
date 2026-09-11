> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Uniform weak factorial bounds for the actual two-electron KS pullbacks

This result is formalized in `lean/CoulombKSPhysicalFactorial_v1.lean`. It supplies the actual solution input needed for the next pointwise and KS descent steps; it does not complete Theorem T.

Fix real charge and energy parameters Z and E. There exist constants C_H, M, A at least one, depending only on Z and E, with the following property. Let f be an actual scalar L² function satisfying the weak H² two-electron Coulomb graph equation H f = E f. Let g be a continuous representative of f that is L-Lipschitz on the physical ball of radius R about the origin. For every positive ε ≤ min(1,R/4), every unit spectator center t₀, and each of the two nuclear charts and the pair chart, take the literal normalized pullback

    uχ,ε(y,t) = [g(ε Xχ(y,t)) − g(0)] / ε,

where Xχ is the existing physical KS lift composed with the inverse physical spectator reindexing. No trial function or replacement solution is introduced.

Set V to the actual product volume of the radius-two closed ball at zero in the canonical four-plus-three coordinate space. This is a finite fixed constant, independent of chart, center and scale. Put

    W = (L² + |g(0)|²) C_H,
    F₀ = M |g(0)| sqrt(V),
    C = max(fixedBoxFactorialConstant(1,M), fixedBoxFactorialConstant(4,M)).

On the coordinate box centered at (0,t₀), with all half-widths 1/128, there exists a single family Fαβ of genuine weak Y/T derivatives, with F₀₀ equal to the literal pullback. That same family has finite L² budgets at every finite order. Its actual weighted local profile on the box with half-widths 1/256 satisfies, for every natural order r,

    N_r ≤ 12 C A (F₀ + 498 sqrt(W)) (3072 C A)^r r!.

Here N_r is exactly `factorialLocalProfile` from `GrushinFactorialLocalProfile_v1.lean`; its finiteness is separately included in the theorem. The profile uses its existing finite set of 498 weighted derivatives; this is distinct from the trial dictionary in Theorem T. The one family is selected before all derivative orders. The constants C_H, M and A are selected before the solution, its representative, L, R, ε, chart and unit center.

The proof composes the actual physical inhomogeneous weak equations on the larger 1/64 box, common coefficient/source factorial bounds, exact measure and weak-derivative reindexing, the previously proved physical H12 estimate, and the local factorial theorem. The principal constants are c=4 for a nuclear chart and c=1 for the pair chart. The coefficient is ε b(Z,εE); the source is b(Z,εE)(−g(0)). In particular, the source does not acquire an extra ε. The boxes include the selected KS collision fiber y=0.

The final source compiles in the pinned Lean 4.34.0-rc2 environment. Its two declarations pass strict v8 expanded-statement and axiom auditing with only propext, Classical.choice and Quot.sound. The exact predicate and fixed-volume definition were additionally printed and inspected. Pinned dependency objects were reused; this checkpoint is not an isolated source rebuild. Exact receipts, hashes and independent review are recorded in `COULOMB_KS_PHYSICAL_FACTORIAL_CHECKPOINT_v1.json`.

This is a theorem about supplied scalar Coulomb eigenfunctions and explicitly supplied continuous local Lipschitz representatives. It does not assert their existence for arbitrary Z,E. The full fermionic ground-state instantiation, pointwise derivative bounds, smooth representatives, quantitative KS descent, global H² approximation, solver certification and full Theorem T remain separate obligations.

Frozen target provenance: `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. All frozen sources and prior PASS artifacts are preserved.
