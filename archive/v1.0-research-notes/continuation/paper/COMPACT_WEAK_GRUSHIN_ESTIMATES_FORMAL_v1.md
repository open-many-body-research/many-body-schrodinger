> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact weak H² Grushin estimates

Evidence category: fully formalized mathematical result. Six new modules and 36 declarations compile and pass an expanded-statement and full axiom audit, with only propext, Classical.choice, and Quot.sound. The main theorem is TheoremT.Continuum.WeakGrushin.compact_weakH2_estimates.

Let y range over R⁴ and t over any finite Euclidean coordinate space, with actual product Lebesgue measure. Let c≥0. Suppose f is an actual L² function vanishing almost everywhere outside some compact K, with actual L² witnesses d(v) and e(v,w) satisfying all real compact smooth weak tests for D_v f and D_w D_v f. Set y_i=(basis_i,0), t_j=(0,basis_j), T_c e=c|y|² Σ_j e(t_j,t_j), and P_c e=−Σ_i e(y_i,y_i)−T_c e. These are actual pointwise expressions in L² representatives, not arbitrary operator graph assumptions.

The theorem proves P_c e∈L² and the following estimates, with every integral over actual configuration product space:

16c Σ_j ∫|d(t_j)|² ≤ ∫|P_c e|²,

Σ_i,k ∫|e(y_i,y_k)|² + ∫|T_c e|² + 2c Σ_i,j ∫|y|²|e(y_i,t_j)|² ≤ (3/2)∫|P_c e|².

All ordered Y-Hessian entries occur. Zero c and an empty spectator coordinate type are included. Unweighted spectator coercivity requires positive c when the first inequality is rearranged.

The proof obtains the previously verified ordinary-product compact H² approximation internally. Every smooth approximant has support inside one fixed compact L. A generic support lemma proves that all first/second derivative representatives and their strong L² limits vanish outside L. Every continuous real weight is bounded after extension by zero outside L; the actual multiplication agrees with this bounded extension almost everywhere. Consequently the required weighted derivatives and finite weighted sums converge in L², and all squared integral norms converge. The smooth compact Grushin estimates then pass to the limit with their constants unchanged. No density or weighted convergence hypothesis is supplied to the main theorem.

This is an estimate for inputs already known to lie in actual weak H². It does not assert that a general weak solution with P_c f∈L² is jointly H². It does not yet supply the local H¹-to-anisotropic-gain theorem, the partial regularization μ→0 passage, analytic regularity, a rate, a numerical algorithm, or full Theorem T. The exact compact-test identity identifying the principal weak-jet expression with a supplied weak Grushin PDE output is a separate next bridge.

These six modules reuse pinned Mathlib and project object caches for development. They lie outside the sealed 671-target v18 isolated-source rebuild. No frozen artifact or successful earlier proof was changed. Preservation reference: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09; frozen RWA_REPORT.md SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066.
