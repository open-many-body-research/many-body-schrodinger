> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent bounded review of the proposed gap-free alternative

Date: 2026-09-09. This is a review of the explicit formulas communicated by the arbitrary-electron-count subtask and of `../arbitrary_n/ARBITRARY_N_SCOPE_v1.md`. At the time of this note its announced detailed companion `GAP_FREE_COMPUTABILITY_v1.md` had not yet been written; this is therefore not a review of that companion's final algorithm or every statement. No frozen artifact is altered. Historical provenance remains commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`; the source formulas reviewed here are new post-freeze work.

The communicated continuum bounds survive the following independent calculation. This supports a paper route to computability after its effective box construction is supplied. It does not establish a verified executable, a Lean theorem, a precision-polynomial cost, or novelty.

Write \(T=\frac12\sum_i\|\nabla_i\psi\|^2\), and let \(\lambda_N(R)\) be the Dirichlet form ground energy in \((-2R,2R)^{3N}\) with full fermionic spin symmetry. A Lipschitz one-electron partition \(\chi^2+\eta^2=1\), with angle changing by \(\pi/2\) across a transition of width \(R\), has gradient-square sum at most \(\pi^2/(4R^2)\). Its tensor IMS kinetic error is at most \(N\pi^2/(8R^2)\).

The all-interior sector belongs to the Dirichlet form domain. Each other sector has \(k<N\) interior electrons. Its function remains antisymmetric within that group, so its retained interior Hamiltonian is bounded below by \(E(k,Z)\ge E(N-1,Z)\), using the usual variational monotonicity. Every exterior electron has Euclidean nuclear distance at least \(R\). Dropping exterior kinetic terms and all repulsion involving exterior electrons gives the lower bound \(E(N-1,Z)-NZ/R\). The sum over sectors therefore gives

\[
E(N,Z)\ge\min\{\lambda_N(R),E(N-1,Z)-NZ/R\}-N\pi^2/(8R^2).
\]

The upper bound \(E(N,Z)\le\min\{\lambda_N(R),E(N-1,Z)\}\) follows from zero extension and sending the last electron to infinity. For \(N\ge1\) the resulting recursive bounds can shrink as \(R\to\infty\), regardless of binding or a spectral gap. The \(N=0\) base case is exactly zero.

For clipping \(r^{-1}\) at height \(M\), the useful sharp elementary pointwise bound is

\[
0\le(r^{-1}-M)_+\le(4Mr^2)^{-1}.
\]

Sliced Hardy gives nuclear form error at most \((2Z/M)T\). In relative pair coordinates, \(\|\psi/r_{ij}\|^2\le\|\nabla_i\psi-\nabla_j\psi\|^2\le2(\|\nabla_i\psi\|^2+\|\nabla_j\psi\|^2)\). Summing the clipped pair errors gives at most \(((N-1)/M)T\). Thus the stated coefficient \((2Z+N-1)/M\) is correct. Using merely \((r^{-1}-M)_+\le1/(Mr^2)\) would unnecessarily lose a factor four.

Both original and clipped box forms are bounded below by \(T/2-NZ^2\), since clipping nuclear attraction weakens it and clipped repulsion stays nonnegative. If one computable anchor bound \(U\) bounds both ground energies from above, their minimizing sequences have kinetic energy bounded by \(2(U+NZ^2)\), giving the communicated two-sided clipping error. A single common \(U\) must be specified; an upper bound for only one clipped form cannot silently serve both. It can be obtained from a fixed finite sine-Slater trial by discarding attraction and bounding repulsion.

For a bounded clipped potential of norm at most \(B\), a fermionic kinetic spectral projector \(P\) with complement kinetic energy at least \(\Lambda\) gives the block bound

\[
\lambda_M\ge\min\{\lambda_P-\varepsilon,\Lambda-B-B^2/\varepsilon\},
\]

by bounding the off-diagonal potential term with \(2Bxy\le\varepsilon x^2+B^2y^2/\varepsilon\). If the anchor lies in \(P\), \(\lambda_P\le U\), and \(\Lambda\ge U+B+B^2/\varepsilon\), this yields \(\lambda_P-\varepsilon\le\lambda_M\le\lambda_P\). The projector should be defined by an explicit integer cutoff on sums of sine-mode squares; rational bounds on \(\pi^2\) make a sufficient kinetic threshold effective without exact transcendental comparisons.

The remaining work is substantive but concrete: specify finite enumeration and spin antisymmetry, a computable common anchor bound, signed interval assembly of all clipped matrix entries, rational PSD enclosure with perturbation tolerances, and the error schedule composing recursion, localization, clipping, and projection. Compact Lipschitz quadrature is an available route because the clipped Coulomb function is bounded and Lipschitz; all constants, sine evaluations, and determinant normalization must be included. Finite matrices used with the displayed continuum bracketing are approximations to the original operator, not altered definitions of its energy. No uniform efficiency follows from this construction.
