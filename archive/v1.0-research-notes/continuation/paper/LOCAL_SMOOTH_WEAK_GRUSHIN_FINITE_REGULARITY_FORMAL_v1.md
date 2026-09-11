> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Arbitrary finite weak regularity on interior Grushin boxes

Let Ω be an open subset of R⁴×R³ and c>0. Suppose B:Ω→R and s:Ω→C are smooth, and f is locally L² and solves the actual distributional equation

    (−Δ_Y − c|Y|² Δ_T + B) f = s.

Fix a closed rectangular outer box contained in Ω and a concentric inner box with positive strictly smaller Y and T half-widths. For every natural number m, the Lean theorem `local_smooth_weak_grushin_finite_regularity` constructs all coordinate weak derivatives through total order m on the open inner box. Every derivative has a genuine restricted-volume L² representative; one finite nonnegative constant W bounds the squared L² norm of every coordinate word of length at most m. The zero word is exactly f, and all successive first-direction weak identities are included.

The proof supplies all premises of the abstract finite composition. Smooth complex source words are actual ordered Fréchet directional derivatives and satisfy integration by parts. Compactness bounds the finitely many needed derivatives of the source and real potential. The source bounds give actual region L² budgets, including integrability. The quadratic Grushin coefficient has the previously proved all-word bound R²+2R+2 on a Y-radius-R box. A schedule of 2m actual pairs of compact cutoffs is chosen from box geometry and m alone. The first m stages gain spectator derivatives; the remaining m stages recover two Y levels at a time, after deriving the required differentiated equations. Restricting the larger Y reserve to total order m yields all interleaved coordinate chains.

Only raw local L² and the original weak equation are assumed for f. No H², preliminary solution derivative, or higher differentiated solution equation is an input. The intermediate abstract theorem retains finite source data and cutoff hypotheses; the final theorem discharges them. The case m=0 is included by the zero-stage states. Interior positivity supplies the compact collars for positive orders.

This is a finite weak regularity license for later commutator proofs. The bound depends on m, the coefficient, source, solution and geometry; no bound uniform in m, factorial rate, analytic continuation radius, smooth pointwise representative, or equality to a library Sobolev-space definition is asserted. A different family may be chosen at each requested order. Classical choices of bounds and derivative representatives are not executable algorithms.

The four new source modules are `FiniteWeakGrushinCoordinateRegularity_v1`, `SmoothComplexMixedSourceWords_v1`, `SmoothComplexMixedSourceBounds_v1`, and `LocalSmoothWeakGrushinFiniteRegularity_v1`. All compile and pass the approved v6 strict audits, covering 21 declarations. Expanded statements and standard foundational axiom dependencies were inspected. The audit rejects failed/fallback pretty-print output as well as ellipses. The earlier known v5 printer failure is handled by its separate preserved correction; it did not affect these statements.

Pinned library and previously compiled dependency objects were reused. These modules postdate the earlier 671-target isolated desktop source rebuild and are not covered by that rebuild. Frozen sources and prior successful source bytes remain unchanged. This result does not establish Theorem T or its approximation rate.
