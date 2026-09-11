> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Generic compact tests and tempered derivatives, version 1

For any finite-dimensional real inner-product space E with its actual Lebesgue measure, the following statements are now Lean-verified for actual complex L² classes.

If f,w∈L² and ∫φw=∫(Δφ)f for every real C∞ compactly supported φ, then Δf=w as tempered distributions. Consequently f has L² weak first derivatives in every direction, and all ordered second weak derivatives in every pair of directions. The final compact-test hypothesis contains no derivative-existence or regularity premise.

For any f,g∈L² and any direction v, the actual weak identity ∫φg=−∫(D_vφ)f for all real C∞ compact tests is equivalent to D_v f=g in tempered distributions. This supplies the converse to the earlier distribution-to-compact-test bridge.

The compact-to-Schwartz passage is proved directly. A smooth bump χ(x/R), equal to one on the radius-R ball and compactly supported in the radius-2R ball, has first and second directional derivatives bounded by C/R and C/R². For R=n+1, dominated convergence gives the zeroth, first, and second cutoff pairing limits. Hölder supplies the integrability of every Schwartz-derivative/L² pairing. Real and imaginary parts extend the hypothesis to complex compact tests; finite orthonormal-basis sums identify the Laplacian. There is no assumed density theorem or approximation convergence premise.

`GenericDistributionLaplacianConverse_v1` contains the Laplacian converse and the genuine weak second-jet consequence. `GenericDistributionDirectionalConverse_v1` contains the directional equivalence. The actual Cartesian-product transport is separately sealed in `PRODUCT_COMPACT_LAPLACIAN_CONVERSE_CHECKPOINT_v1.json`.

Evidence: eight modules, 35 declarations, exact final source compilations and strict expanded-statement/complete-axiom audit `20260910T164951_152734Z`; only propext, Classical.choice and Quot.sound occur. The derivative witnesses are mathematical existence witnesses, not an executable solver. Pinned Mathlib, prior-audit and continuation objects were reused. These new modules are outside the completed 671-target isolated source rebuild.

This establishes a global ordinary-elliptic prerequisite. It does not yet establish local weak Grushin gain, any quantitative local bound, analyticity, factorial estimates, certified two-electron computation, or full Theorem T. No novelty claim is made.

Preservation: new continuation files only. The frozen lineage is commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09, `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md` SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066. No frozen or successful source bytes were changed.
