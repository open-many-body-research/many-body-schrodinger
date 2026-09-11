> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Full product weak H² from genuine diagonal derivatives

Let Y and T be arbitrary finite-dimensional real inner-product spaces with their Lebesgue measures, and let bY and bT be orthonormal bases indexed by finite types. The ordinary product Y×T retains its actual product measure and maximum norm. Write vᵢ for the pure factor basis directions, indexed by the disjoint union of the two index types.

The new theorem assumes only an actual complex L² class f and actual L² classes dᵢ,eᵢ satisfying

\[
D_{v_i}f=d_i,\qquad D_{v_i}d_i=e_i
\]

against every real smooth compactly supported test. It constructs all genuine L² first derivatives a(v) and all ordered second derivatives b(v,q), for every pair of product-space directions. In particular, it constructs the mixed derivatives. The resulting jets satisfy a(vᵢ)=dᵢ and b(vᵢ,vᵢ)=eᵢ as equalities of actual L² classes.

The proof first constructs the actual L² trace w=Σᵢeᵢ. Two genuine weak integrations by parts in each coordinate prove the compact-test identity Δf=w. The already verified `ProductCompactLaplacianConverse_v2` transports this identity to the Euclidean copy `WithLp 2 (Y×T)` and applies the Fourier L² elliptic gain. Transport back preserves the actual product measure. Weak derivative uniqueness proves compatibility with every supplied coordinate witness.

No mixed derivative, full weak H² regularity, compact support of f, convergence of derivatives, density theorem, or distributional Laplacian output is assumed as an extra premise. In particular the Laplacian output is constructed from the supplied diagonal data. The theorem is qualitative existence of actual derivative witnesses, not an executable selection procedure.

A companion generic Fourier estimate is proved for any finite-dimensional real inner-product space E:

\[
\|D_qD_v f\|_2\le \|v\|\,\|q\|\,\|\Delta f\|_2.
\]

The product-space composition consequently yields

\[
\|b(v,q)\|_2\le
\|\operatorname{toLp}_2v\|\,
\|\operatorname{toLp}_2q\|\,\|\textstyle\sum_i e_i\|_2.
\]

These direction norms are those of the Euclidean copy. Replacing them silently by the ordinary product maximum norms would be incorrect. For every pure factor basis pair, both norms are one, so every ordered coordinate mixed derivative has L² norm at most the L² norm of the actual diagonal trace. This checkpoint does not claim a sharp aggregate full-Hessian identity.

The declarations are in `ProductDiagonalWeakH2_v1`, `ProductDiagonalWeakH2Compatible_v1`, `GenericWeakMixedLaplacianNorm_v1`, and `ProductDiagonalWeakH2Norm_v1`. Expanded statements and full axiom dependencies are audited with the standard foundational axioms `propext`, `Classical.choice`, and `Quot.sound` only. Source and object hashes and receipts are in `audits/PRODUCT_DIAGONAL_WEAK_H2_CHECKPOINT_v1.json`. Development builds reuse pinned library and project object caches; these modules postdate the completed v18 source-rebuild snapshot.

This is a shared regularity prerequisite for the planned two-step Grushin argument. It is not itself the anisotropic-to-H² composition, an analyticity theorem, an approximation rate, a numerical algorithm, or full Theorem T.

Frozen artifacts are unchanged. The original `RWA_REPORT.md` SHA-256 is `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, freeze `THEOREM_T_FREEZE_2026-09-09_212604`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag `theorem-t-proof-freeze-2026-09-09`.
