> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Sharp weak L² Hessian identity and diagonal-data composition

For any finite-dimensional real inner-product space E and any orthonormal basis (vᵢ), the new generic theorem proves

\[
\sum_{i,j}\|D_{v_j}D_{v_i}f\|_2^2=\|\Delta f\|_2^2
\]

from genuine actual L² first and ordered second weak derivative witnesses and an actual L² distributional Laplacian. No support, density, approximation, or convergence hypothesis is assumed. The proof establishes all finite Fourier derivative identities on one common almost-everywhere set, applies the orthonormal basis identity pointwise, and uses proved finite-sum integrability and Parseval. A separate arbitrary-measure L² finite-sum lemma keeps the analytic identity distinct from elaboration details.

The product transport uses the exact measure-preserving Euclidean copy of the ordinary product Y×T. In combination with the already sealed diagonal-to-H² theorem, it proves a stronger statement whose inputs consist only of actual L² coordinate first derivatives dᵢ and same-coordinate second derivatives eᵢ. The all-direction first and ordered second jets are constructed, agree with the supplied coordinate data, and satisfy

\[
\sum_{i,j}\|b(v_i,v_j)\|_2^2
=\|\textstyle\sum_i e_i\|_2^2.
\]

Thus the aggregate Hessian estimate introduces no factor depending on the dimension. The right side is the norm of the actual L² sum, not the sum of the squared diagonal norms. No inequality reversing these two quantities is claimed.

The new sources are `GenericWeakHessianLaplacianIdentity_v1` and `ProductDiagonalWeakH2Hessian_v1`. The first has three declarations, including the generic finite-sum lemma; the second has three declarations, including the final construction from diagonal data. Strict expanded-statement/axiom receipts, exact source/object hashes, and build disclosure are recorded in `audits/PRODUCT_WEAK_HESSIAN_IDENTITY_CHECKPOINT_v1.json`. All declarations use only the standard foundational axioms. Pinned library and project development caches were reused. These modules are outside the completed v18 isolated source-rebuild snapshot.

This sharpens `PRODUCT_DIAGONAL_WEAK_H2_CHECKPOINT_v1.json` without altering any of its sealed source. It remains a continuum regularity theorem; it is not an executable solver, an analytic approximation rate, a numerical interval, a novelty claim, or full Theorem T.

Frozen artifacts remain unchanged: original `RWA_REPORT.md` SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, freeze `THEOREM_T_FREEZE_2026-09-09_212604`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.
