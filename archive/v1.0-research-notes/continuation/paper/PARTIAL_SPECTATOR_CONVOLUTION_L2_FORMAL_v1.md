> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual partial spectator convolution in L², version 1

Let Y and T be arbitrary finite-dimensional Euclidean spaces with their actual Lebesgue measures, let G:Y×T→ℂ belong to L², and let K:T→ℝ be integrable. The actual Bochner integral

H(y,t) = ∫ K(s) G(y,t−s) ds

has an integrable integrand for almost every (y,t), defines an L² function, and satisfies

‖H‖₂ ≤ (∫|K|) ‖G‖₂.

No separate pointwise measurability premise is required for either input. The theorem applies to every representative satisfying the actual MemLp hypothesis. Almost-everywhere equal G inputs give almost-everywhere equal outputs. Almost-everywhere equal kernels give pointwise equal integral outputs. The generic proof supports a complete real-inner codomain, an arbitrary SFinite measure on Y, and an SFinite translation- and reflection-invariant measure on a measurable additive commutative group T. Both Euclidean index sets may be empty.

The proof first establishes the scalar-kernel Young estimate on each T fiber, with p=1 and q=r=2. For strongly measurable representatives, product integration supplies global L² membership and the squared-integral estimate. A separate congruence proof removes the extra representative hypotheses: outside a null set of Y, two AE-equal input functions have AE-equal T fibers; translation and reflection preserve those fiber null sets. Their convolution integrals therefore agree for every t on each good Y fiber. The quasi-measure-preserving first projection lifts this good-fiber condition to product almost-everywhere equality. This step does not invoke a converse to Fubini for arbitrary nonmeasurable predicates.

Integrable K and MemLp G provide strongly measurable representatives, and the proved kernel/input congruence statements transfer the result back to the original actual integrals. Representative selection uses Classical.choice as an analytic proof device. It supplies no executable algorithm.

Six new modules, containing 31 declarations, compile in Lean 4.34.0-rc2 against the pinned Mathlib environment. The exact expanded statements and complete axiom dependencies pass strict audit 20260910T164713_439765Z. Only propext, Classical.choice and Quot.sound occur. Source/object hashes and successful build receipts are sealed in audits/PARTIAL_SPECTATOR_CONVOLUTION_L2_CHECKPOINT_v1.json. Development builds reuse dependency object caches. These six modules are outside the completed 671-target desktop source-rebuild snapshot; no isolated rebuild is claimed for them here.

This proves the stated Young factor, with no optimality or novelty claim. It does not yet establish derivative commutation for weak solutions, convergence of a family of kernels, the weak Grushin derivative gain, or full Theorem T. The next obligation is to construct actual smooth T fibers and their derivative-kernel formulas and bounds, then identify the partially convolved weak equation.

Frozen original: THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md, SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. All frozen and successful prior files remain unchanged.
