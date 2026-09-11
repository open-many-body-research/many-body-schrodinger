> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual anisotropic weak-jet closure under strong L² convergence

This checkpoint proves a conditional analytic closure theorem in Lean. It
does not yet prove the local Grushin gain for every original weak solution.
The missing application premise is a sequence of localized regularizations
with uniformly bounded actual Grushin outputs.

Let Y and T be finite-dimensional real inner-product spaces, equipped with
Lebesgue measure. All functions below are complex L² classes on the ordinary
Cartesian product Y × T. A weak directional derivative means the actual
integration-by-parts identity against every real smooth compactly supported
joint test function. The product model is transported through its Euclidean
copy by exact L² isometries; it is not replaced by an abstract derivative
relation.

Suppose u_n converges strongly in L² to f. For finitely many directions v_i
in Y and w_j in T, suppose u_n has first weak witnesses dY_ni, dT_nj and
ordered second-Y witnesses eYY_nij, with

    D_(v_i,0) u_n = dY_ni,
    D_(0,w_j) u_n = dT_nj,
    D_(v_j,0) dY_ni = eYY_nij.

A uniform bound C on the sum of squared L² norms of these three finite
families yields limit witnesses gY_i, gT_j and hYY_ij with the same aggregate
bound. Every second witness is a weak derivative of the corresponding
constructed first witness. Neither existence of limit derivatives nor
convergence of the approximating derivative sequences is assumed.

If the three groups also satisfy separate bounds CY, CT and CYY, the same
limit witnesses preserve all three bounds as well as the original coupled
bound C. Independent bounded-family constructions are identified by actual
weak-derivative uniqueness. There is no cardinality factor and ordered pairs
are counted exactly once. The result also accepts eventual existence of the
entire finite jet package, with no derivative witnesses for the finitely many
initial sequence terms.

The proof packs the operators D_Y, D_T, and D_Yj composed with D_Yi into one
finite family of continuous linear operators on tempered distributions. The
existing bounded-family L² theorem supplies actual L² representatives of all
limit distributions with its aggregate bound. Distributional derivative
identification and its converse supply the joint compact-test identities.
The first-distribution identity is substituted into each second-distribution
identity, establishing compatibility. This is a mathematical existence
construction using the declared standard foundation, not an executable
algorithm for selecting L² representatives.

For the concrete Grushin operator on R⁴ × R^κ,

    P_c = −Δ_Y − c|y|² Δ_T,       c > 0,

the strongest theorem in this checkpoint is
`TheoremT.Continuum.WeakGrushin.anisotropic_limit_of_eventual_compact_weakH2_outputs`
in `WeakGrushinAnisotropicLimitOutput_v1.lean`. It assumes strong u_n → f and,
eventually n, genuine full weak-H² witnesses for u_n, compact support, the
actual global compact-test equation P_c u_n = h_n, and uniform bounds
||u_n||² ≤ F and ||h_n||² ≤ M. It constructs compatible limit jets satisfying

    Σ_i ||D_Yi f||² ≤ 2F + 3M/4,
    Σ_j ||D_Tj f||² ≤ M/(16c),
    Σ_i Σ_j ||D_Yj D_Yi f||² ≤ 3M/2.

The three constants follow from the previously proved compact weak Grushin
estimates and compact weak directional energy identity, composed in
`CompactWeakGrushinAnisotropicBounds_v1.lean`. No independent first-Y bound
remains in this final theorem. Compact supports may vary with n. Output
convergence is not needed; only a uniform bound on the actual h_n is used.

The earlier separate theorem
`anisotropic_limit_of_compact_weakH2_principal_bound` is preserved as a useful
conditional intermediate result: it assumes a first-Y bound and a uniform
integral bound on the actual principal expression, then derives the 16c and
3/2 estimates. It is not substituted for the stronger output theorem.

No second-T, mixed-YT, full joint-H², analytic regularity, factorial recurrence,
approximation rate, or full Theorem T conclusion is asserted here. The
conditional closure theorem becomes an original-solution gain only after
the localized regularization output bound is established and supplied.

All eight new modules compile in pinned Lean 4.34.0-rc2. Strict audits print
complete expanded final statements and every local declaration's axiom
dependencies. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
Compilation and auditing reuse existing pinned dependency objects; these
sources are outside the completed 671-target desktop source-rebuild snapshot.
The accompanying checkpoint records exact sources, objects, receipts and
hashes. A focused independent read-only review found no concrete error in
the packed operator-family argument or compatibility proof; that review is
not a substitute for compilation or semantic assessment.

Frozen historical reference: commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`, report
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
Frozen and previously successful sources and receipts are unchanged.
