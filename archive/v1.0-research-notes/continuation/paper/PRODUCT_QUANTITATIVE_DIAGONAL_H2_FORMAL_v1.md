> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Quantitative full joint weak H² from finite diagonal data

Let Y,T be arbitrary finite-dimensional real inner-product spaces with orthonormal bases indexed by finite types ι,κ. Set D=|ι|+|κ|. On the actual ordinary product with Lebesgue measure, let f,dᵢ,eᵢ be actual complex L² classes satisfying the genuine compact-test weak equations Dᵥᵢf=dᵢ and Dᵥᵢdᵢ=eᵢ for every factor-coordinate basis direction vᵢ.

The new theorem constructs all first jets a(v) and all ordered second jets b(v,q), and proves their exact compatibility with the supplied coordinates. In particular, their squared first-gradient sum is preserved:

\[
G=\sum_i\|a(v_i)\|_2^2=\sum_i\|d_i\|_2^2.
\]

The full ordered Hessian sum obeys

\[
H=\sum_{i,j}\|b(v_i,v_j)\|_2^2
=\|\textstyle\sum_i e_i\|_2^2
\le D\sum_i\|e_i\|_2^2.
\]

The equality is the previously verified sharp Fourier Hessian identity. The inequality is a proved finite vector-sum bound. Thus the dimension factor enters only when individual diagonal squared norms replace the actual trace norm.

The explicitly defined full joint squared H² quantity is Q=‖f‖²+G+H, using every ordered coordinate second derivative. If ‖f‖²≤C0, Σ‖dᵢ‖²≤C1, and Σ‖eᵢ‖²≤C2, the constructed genuine jets satisfy

\[
Q\le C0+C1+D\,C2.
\]

This is a bound on the displayed actual Sobolev quadratic quantity; the module does not introduce a separate normed Sobolev-space instance or a discretized replacement.

A grouped version retains the factor dimensions m=|ι| and n=|κ|. For the same jets and every positive τ,

\[
H\le(1+\tau)m\sum_{i\in\iota}\|e_i\|_2^2
 +(1+1/\tau)n\sum_{j\in\kappa}\|e_j\|_2^2.
\]

Adding ‖f‖²+G gives the corresponding full bound. Setting τ=1 yields the coefficients 2m and 2n; the free parameter can adapt to unequal block bounds. No universal strict improvement over the total-dimension bound is claimed. Empty index types are permitted throughout.

`FiniteLpTraceBounds_v1` contains four generic finite norm inequalities. `ProductDiagonalWeakH2Quantities_v1` defines the actual coordinate quadratic quantities and proves first-gradient preservation. `ProductDiagonalWeakH2Quantitative_v1` constructs the genuine jets and proves total-dimension and scalar-input bounds. `ProductDiagonalWeakH2Grouped_v1` proves the grouped family. Their exact source/object hashes and strict expanded-statement/axiom receipts are in `audits/PRODUCT_QUANTITATIVE_DIAGONAL_H2_CHECKPOINT_v1.json`. Standard foundational axioms only; pinned library and project object caches reused. These modules postdate the completed v18 isolated source rebuild.

No mixed-derivative existence, full H² assumption, compact support, or derivative convergence is an input premise. This is the quantitative diagonal-to-full-H² step needed after the two anisotropic gains. It is not the two-step Grushin composition itself, an analyticity estimate, a numerical algorithm, or full Theorem T.

Frozen artifacts remain unchanged: original `RWA_REPORT.md` SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, freeze `THEOREM_T_FREEZE_2026-09-09_212604`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.
