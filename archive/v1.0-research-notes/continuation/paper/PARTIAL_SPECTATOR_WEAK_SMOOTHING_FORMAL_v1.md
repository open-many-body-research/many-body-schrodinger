> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# All ordered weak spectator derivatives of partial smoothing, version 1

Let Y,T be finite-dimensional real inner-product spaces with actual product Lebesgue measure, let G:Y×T→ℂ belong to L², and let K:T→ℝ be C∞ and compactly supported. Define H(y,t)=∫K(s)G(y,t−s)ds by the actual Bochner integral. Almost every T fiber of H is C∞.

For every finite ordered list V of T directions, recursively differentiate the actual fiber t↦H(y,t) in those directions. The resulting function J_V belongs to L²(Y×T), and

‖J_V‖₂ ≤ (∫|D_V K|) ‖G‖₂.

For every direction v∈T and every real C∞ compactly supported joint test φ:Y×T→ℝ,

∫ φ J_(v::V) = −∫ D_(0,v)φ J_V.

Thus these are genuine weak derivatives on the product, not only fiberwise formal expressions. The Lean class `partialSpectatorJetLp hK hcK hG V` is represented by J_V, and `partialSpectatorJetLp_weak_derivative` states exactly `WeakProductL2Directional` between consecutive classes. G needs only the actual MemLp hypothesis.

The proof first invokes the compact-kernel convolution differentiation theorem on each good L² fiber. Induction shows J_V equals convolution with D_V K pointwise for every t on that fiber. Product Young estimates imply global L² membership and the norm bound. Compact joint tests times these L² functions are integrable. Fubini and ordinary fiber integration by parts give the displayed joint weak identity. The actual chain rule identifies the fiber test derivative with D_(0,v)φ. No differentiability in Y is assumed or inferred.

The four modules PartialSpectatorSmoothKernel_v1, PartialSpectatorKernelJets_v1, SpectatorFiberWeakTest_v1 and PartialSpectatorWeakJets_v1 contain 21 declarations. Exact expanded statements and complete axiom reports pass strict audits 20260910T165110_144363Z and 20260910T165547_945868Z. Only propext, Classical.choice and Quot.sound occur. Sources and objects are hash-bound in audits/PARTIAL_SPECTATOR_WEAK_SMOOTHING_CHECKPOINT_v1.json. Pinned dependency caches are reused; these modules are outside the completed 671-target desktop source-rebuild snapshot.

The constants depend on the L¹ norms of kernel derivatives and need not remain bounded as a kernel narrows. No regularity in Y, uniform weak Grushin gain, approximation rate, or full Theorem T follows from this checkpoint. The next use is to commute the actual weak Grushin equation with partial convolution and recover a locally L² full Laplacian before deriving uniform estimates. Noncomputable L² representatives in this analytic proof do not constitute an executable solver. No novelty or optimality is claimed.

Frozen original: THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md, SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. All frozen and successful prior files remain unchanged.
