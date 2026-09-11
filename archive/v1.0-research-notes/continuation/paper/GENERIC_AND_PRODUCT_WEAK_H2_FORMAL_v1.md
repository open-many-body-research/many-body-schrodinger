> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Generic and product-space weak H² elliptic gain, version 1

For every finite-dimensional real inner-product space E with its actual Lebesgue measure, let f,w be complex L² classes. If their actual tempered distributions satisfy Δf=w, there exist L² first derivative witnesses d(v) for every v∈E and L² ordered second derivative witnesses e(v,q) for every v,q∈E. They satisfy

∫ φ d(v) = −∫ D_vφ f,

∫ φ e(v,q) = −∫ D_qφ d(v)

for every real C∞ compactly supported φ. Restricting the directions to an orthonormal basis supplies all genuine weak first and mixed second derivatives. The Laplacian premise is an equation for the input distribution; no derivative-existence or regularity conclusion is assumed.

`GenericWeakEllipticGain_v1.lean` also proves for every natural n that actual Mathlib `MemSobolev n 2` implies recursively defined order-n weak regularity with L² witnesses in all ordered directions. Witnesses are noncomputably chosen. This analytic implication is not an executable derivative-finding algorithm.

The proof uses the already generic `LaplacianSobolevBridge_v1.lean`. Under Mathlib's Fourier convention exp(−2πi⟨x,ξ⟩), the order-two Bessel potential is f−(2π)⁻²Δf. Thus the given L² Laplacian produces order-two Bessel-potential membership. Mathlib's proved Sobolev derivative theorem supplies L² distributional derivative witnesses. Applying their distributional identities to the Schwartz function obtained from each compact real smooth test gives the genuine weak identities above.

`ProductWeakEllipticGain_v1.lean` supplies the exact norm/measure transport for KS products. For finite-dimensional real inner-product factors Y,T, the ordinary product Y×T has the maximum norm and product Lebesgue measure. Its Euclidean copy is `WithLp 2 (Y×T)`. The maps `WithLp.toLp/ofLp` are continuous linear equivalences, are exactly measure preserving, and induce complex L² linear isometries. The theorem transfers the compact-test identities and the ordered derivatives back to the ordinary product. No assumption identifies the maximum norm with a Euclidean norm.

The product theorem takes the actual equation Δ(lift f)=lift w on this explicitly defined Euclidean copy, and returns weak L² first and mixed second derivatives for the original product function f. `ProductDistributionLaplacian_v1.lean` makes the equation concrete: for arbitrary orthonormal bases (a_i) of Y and (b_j) of T, its Laplacian equals exactly

Σ_i D_(a_i,0)² + Σ_j D_(0,b_j)²,

with directions lifted by `WithLp.toLp 2`. This holds for every tempered distribution. The composed theorem accepts precisely this summed factor-direction equation and concludes the actual ordinary-product weak H² witnesses. It applies to Y=R⁴ and every finite-dimensional spectator space, including nuclear KS dimension 3N+1. It does not require dimension divisible by three or a nonempty spectator index.

All three new modules compile in Lean 4.34.0-rc2. Strict audits check complete expanded statements and complete axiom reports; only `propext`, `Classical.choice`, and `Quot.sound` occur. The checkpoint binds sources, objects and audit receipts by SHA-256. Development builds reuse the pinned Mathlib, prior-audit and continuation object caches. These three sources have not yet undergone an isolated dependency source rebuild.

This result does not establish local weak Grushin gain, the arbitrary-product compact-test-to-Schwartz converse, partial-regularization convergence, a quantitative local estimate, analyticity, factorial bounds, an approximation rate, or full Theorem T. The next use is to justify ordinary second weak derivatives of a localized, partially regularized Grushin solution once its full factor-coordinate distributional Laplacian is shown to be L².

Frozen artifacts remain unchanged: commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`, snapshot `THEOREM_T_FREEZE_2026-09-09_212604/`. Frozen `RWA_REPORT.md` SHA-256: `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`. This is a reusable formalization/generalization of standard elliptic regularity, with no novelty claim.
