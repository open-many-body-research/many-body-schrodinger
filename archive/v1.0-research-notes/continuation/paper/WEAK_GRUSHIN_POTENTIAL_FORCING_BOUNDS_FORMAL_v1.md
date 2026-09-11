> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact L² bounds for potential forcing, version 1

This checkpoint formalizes the quantitative coefficient estimates used when a weak Grushin equation is differentiated in spectator directions. It proves estimates for the actual complex-valued products and their Lebesgue integrals. It does not assume or establish a weak derivative or PDE relation for the supplied data.

Let Y and T be finite-dimensional real inner product spaces, let K be compact and contained in Ω, and let the direction index set I be finite. Let G and d_j be locally L² on Ω, and let real B and A_j be continuous on Ω. Suppose on K that

\[
 |B|\le b,\qquad \sum_{j\in I}|A_j|^2\le b_1^2.
\]

Then BG and every R_j = −A_jG − Bd_j belong to L²(K); their squared norms are integrable, and

\[
 \int_K|BG|^2\le b^2\int_K|G|^2,
\]
\[
 \sum_j\int_K|R_j|^2
 \le 2b_1^2\int_K|G|^2+2b^2\sum_j\int_K|d_j|^2.
\]

The coefficient squares are summed before using their bound. No cardinality factor is inserted. The supplied aggregate bound b₁ may itself depend on the dimension or on the direction family; this result makes no dimension-independent claim about b₁. No sign assumption on b₁ is needed. Empty index sets, empty K, and zero restricted measure are permitted.

The actual smooth-potential specialization assumes Ω open, B ∈ C∞(Ω), and arbitrary spectator vectors v_j ∈ T; it sets A_j(x)=fderiv ℝ B x (0,v_j). Here G and d_j are actual global complex L² elements. This derivative is continuous on Ω by the proved local smooth-derivative infrastructure. No behavior of B outside Ω is required. The direction vectors need not be orthogonal for this coefficient estimate.

An intermediate theorem works on an arbitrary measure space with B,A_j ∈ L∞, G,d_j ∈ L², and the coefficient inequalities holding almost everywhere. All L² membership and square-integrability are proved before integral comparison or finite-sum interchange. No finite-measure or sigma-finiteness assumption is used in this intermediate theorem. Its outputs do not assert unweighted L¹ integrability on an arbitrary infinite measure space.

## Formal evidence

Five exact declarations in three new modules compile and have complete expanded-statement and axiom audits:

- `WeakGrushinPotentialForcingPointwise_v1`: `potential_smul_norm_sq_le`, `potential_spectator_forcing_sum_norm_sq_le`.
- `WeakGrushinPotentialForcingIntegral_v1`: `potential_forcing_integral_bounds`.
- `WeakGrushinPotentialForcingCompact_v1`: `compact_continuous_potential_forcing_bounds`, `compact_spectator_potential_forcing_bounds`.

All lie in `TheoremT.Continuum.WeakGrushin`. Strict receipts are `audits/formal_semantics/20260910T182413_745977Z/receipt.json` and `audits/formal_semantics/20260910T182907_644024Z/receipt.json`. Only `propext`, `Classical.choice`, and `Quot.sound` occur. The checkpoint records current source/object hashes, compile receipts, logs, and the independent focused review. Reviewer agreement is not proof.

The Lean environment is the pinned v4.34.0-rc2 toolchain, using existing pinned library/prior-audit objects and newly compiled continuation objects. These three sources are outside the completed 671-target desktop source-rebuild snapshot. This checkpoint does not claim a fresh source dependency rebuild.

## Scope and next obligation

These are fully formalized coefficient-estimate theorems with explicit hypotheses. They quantify the actual potential forcing in the preceding weak differentiation result. They do not prove existence of G, derivative witnesses, uniform coefficient bounds, a PDE gain, analytic regularity, an approximation rate, or a computational algorithm. No optimality or novelty is claimed. The next composition uses these bounds in the quantitative second local Grushin gain, retaining the dependence of b,b₁ and the cutoff geometry.

Frozen reference: `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Frozen and prior successful source bytes remain unchanged; failed development logs are retained.
