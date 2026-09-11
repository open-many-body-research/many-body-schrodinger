> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Full ordered Hessian control for the compact Grushin operator

For any finite family of constant directions v_i in a finite-dimensional real normed space with Haar measure, and every smooth compactly supported function u with values in a real inner-product space, the formal theorem proves

    integral |sum_i D_vi^2 u|^2 = sum_i sum_j integral |D_vj D_vi u|^2.

The family need not be a basis or orthogonal. Two integrations by parts and symmetry of the actual second Frechet derivative prove each cross term. This is an exact identity, not an estimate of only the diagonal Hessian entries.

For the actual product Lebesgue measure on R^4 × T, finite-dimensional Euclidean T, complex smooth compactly supported G, and c ≥ 0, write P_c = −Delta_y − c|y|² Delta_t. The new theorem proves

    sum_i,j ||D_yj D_yi G||_2² + ||c|y|² Delta_t G||_2²
      + 2c sum_i,j || |y| D_tj D_yi G||_2² ≤ (3/2) ||P_c G||_2².

All ordered Hessian entries occur. The proof composes the exact identity with the previously audited combined bound. No eigenfunction, spectral, or weak-solution regularity hypothesis is used or discharged. The case c=0 and zero-dimensional T are included; an unweighted tangential gain requires c>0.

Evidence: three source modules, five expanded declarations, compiler exit zero, complete standard foundational axiom reports. Existing pinned development objects were reused. These modules postdate and are outside the sealed 671-target desktop source rebuild. No novelty or optimality claim is made.

Historical anchor: THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md, SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. Frozen artifacts are unchanged. Full Theorem T remains unverified.

Next: extend the compact estimate to genuine weak H² via a fixed-support approximation, then prove the local weak Grushin gain.
