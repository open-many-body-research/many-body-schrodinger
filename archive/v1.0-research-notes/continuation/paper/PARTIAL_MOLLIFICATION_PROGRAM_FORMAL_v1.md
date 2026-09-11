> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual partial mollification: weak equations and convergence, version 1

For arbitrary finite-dimensional real inner-product spaces Y,T, complex G∈L²(Y×T) and integrable real K:T→ℝ, let H(y,t)=∫K(s)G(y,t−s)ds. The already established product Young theorem proves actual Bochner integrability almost everywhere, L² membership and ‖H‖₂≤‖K‖₁‖G‖₂. Smooth compact K additionally supplies all ordered weak spectator derivatives with derivative-kernel norm bounds.

The new pairing identity is

∫ φ H = ∫ K(s) [∫ φ(y,t+s)G(y,t)dy dt] ds

for every continuous compact real test φ. Absolute product integrability is proved from Young applied to |K| and |G|, followed by compact-test multiplication. Fubini and the measure-preserving spectator translation then justify the identity. Almost-everywhere congruence removes additional strong-measurability premises on the inputs.

For Y=KSSpace=R⁴ and any finite family (v_j) of spectator directions, define the actual real test operator

P_cφ = −Σ_(k=1)^4 D_(ksBasis_k,0)²φ − c|y|²Σ_j D_(0,v_j)²φ.

The exact first and second derivatives commute with spectator translation. Consequently, the actual weak equation P_cG=f commutes with partial convolution: P_c(K*_tG)=K*_tf. The global theorem needs only K∈L¹ and G,f∈L²; neither kernel smoothness nor compact kernel support is required. The local theorem permits tests φ for which tsupport(q↦φ(q+(0,s))) lies in Ω whenever K(s)≠0. This support is tsupport(φ)−(0,s); the sign is essential. The weak PDE is an explicit input equation, while its commutation is fully proved.

For an equation (P_c+B)G=f, first form h=f−BG and apply the theorem to P_cG=h. It does not assert K*_t(BG)=B(K*_tG).

Use the actual generic normalized bump kernels K_n on T with inner radius 1/(n+1) and outer radius 2/(n+1). They are nonnegative, C∞, compactly supported and have integral one. The exact L² classes `partialMollifyLp n G` satisfy

‖partialMollifyLp n G‖₂ ≤ ‖G‖₂,

partialMollifyLp n G → G strongly in L²(Y×T).

The proof applies the existing Lebesgue-differentiation-based bump theorem on almost every L² spectator fiber. The set where the resulting sequence converges to G is proved measurable with `measurableSet_tendsto_fun`; only then is the converse product-AE Fubini theorem used. This avoids an invalid lifting of arbitrary nonmeasurable AE fiber predicates. Countably many representative identities give AE convergence of the L² class representatives. The established Hilbert L² convergence theorem combines this AE limit with norm contraction to obtain strong convergence without a finite-volume hypothesis.

For every compact C contained in an open Ω, compact containment gives a positive thickening contained in Ω. Once the actual kernel radius is smaller than this distance, all shifted tests supported in C stay within Ω. Therefore eventually n, the convolved weak equation holds for every C∞ compact test supported in C. This is one threshold for the entire test class, stronger than eventual validity separately for each test. The identity `partialMollifyLp_eq_jet_nil` links these exact approximants to the all-order weak spectator jets.

All new statements compile in Lean 4.34.0-rc2 and pass complete expanded-statement and axiom audits. Only propext, Classical.choice and Quot.sound occur. See the partial convolution, weak smoothing, weak commutation, and normalized convergence checkpoints under audits. Pinned dependency object caches are reused. These sources are outside the completed 671-target desktop source-rebuild snapshot. Representative and bump selection are analytic noncomputable constructions, not an executable solver or a claimed bit-complexity bound.

The next active obligation is to compose these facts with the actual full-Laplacian weak identity to obtain preliminary local H² for each sufficiently narrow mollification, apply uniform localized Grushin estimates, and pass those estimates to the original weak solution. No uniform bound for all kernel derivatives, full weak Grushin gain, factorial recurrence, analytic regularity, approximation rate, or full Theorem T is asserted here. No novelty or optimality claim is made.

Frozen original: THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md, SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. All frozen and successful prior files remain unchanged.
