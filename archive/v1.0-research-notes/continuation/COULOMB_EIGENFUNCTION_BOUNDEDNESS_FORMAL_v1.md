> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Formal global boundedness of continuum Coulomb eigenfunctions

Evidence category: **fully formalized mathematical result**, using the pinned
Lean environment and disclosed development object cache. The exact final
statements and their axiom dependencies are recorded in
`audits/COULOMB_EIGENFUNCTION_BOUNDEDNESS_CHECKPOINT_v1.json`.

For every integer electron count N ≥ 1 and all real Z and E, consider

\[
H_{N,Z}=-\tfrac12\sum_i\Delta_i-Z\sum_i|x_i|^{-1}
             +\sum_{i<j}|x_i-x_j|^{-1}.
\]

The formal input is an actual L² function in the previously established weak
H² graph satisfying Hf = Ef. In the spin theorem the input belongs to the
full fermionic graph, with simultaneous spatial and spin permutations.
No ground-state, binding, isolation, sign, or higher-integrability assumption
is needed. Existence of such a nonzero eigenfunction is not asserted for
arbitrary parameters.

Put d = 3N, χ = d/(d−2), and let S_N be the finite Mathlib Sobolev coefficient
used by `configurationSobolevConstant`. Define

\[
C=2\bigl(|Z|N+\tbinom N2\bigr),\qquad
B=\max\{1,S_N\sqrt{12N(|E|+C^2)}\},
\]
\[
\mathcal M=B^{\chi/(\chi-1)}
                    \chi^{2\chi/(\chi-1)^2}.
\]

The compiled scalar theorem proves

\[
\|f\|_{L^\infty}\le\mathcal M\|f\|_{L^2}.
\]

The compiled spin theorem proves the same constant in

\[
\mathop{\rm ess\,sup}_x
   \left(\sum_\sigma|\psi_\sigma(x)|^2\right)^{1/2}
       \le\mathcal M\|\psi\|_{\rm spin,L^2}.
\]

Here the essential supremum uses Lebesgue measure on actual configuration
space. It does not yet provide a continuous representative or values at
individual collision points. S_N is a specific finite library constant;
this work has not supplied a numerical bound or implementation for it.

The proof proceeds through actual weak H¹ smooth compact approximation and
the Sobolev inequality. A real C¹ chain rule, proved on the actual weak
domain, licenses smooth nonlinear tests

\[
F_r(z)=\left[\frac{b(a+|z|^2)}{b+|z|^2}\right]^r z,
\quad 0<a\le b,\quad r\ge0.
\]

Their physical energy estimate is uniform in a and b. Positive regularization
and cap are removed in actual L² by dominated convergence, with Lq
lower semicontinuity. The resulting gain is

\[
\|f\|_{L^{q_N(2r+1)}}
 \le K_r^{1/(2r+1)}\|f\|_{L^{2(2r+1)}},\qquad
K_r\le B(2r+1)^2,\qquad q_N=2\chi.
\]

Taking 2r+1 = χ^k gives actual membership at every exponent 2χ^k.
The logarithms of the successive coefficient bounds are

\[
w_k=(\log B+2k\log\chi)\chi^{-k}.
\]

Their summability, the uniform finite-iteration bound, and the closed form
of their sum are all compiled. A separate Chebyshev argument proves that
uniform Lp bounds along exponents tending to infinity imply the asserted
essential bound on infinite-volume configuration space. The argument does
not use a finite-measure embedding. The spin result follows by summing the
squares of the component bounds before taking the square root.

For every real Z ≥ 2, a final composition supplies **one and the same**
normalized actual spatial ground eigenfunction at the full fermionic spectral
bottom that is real almost everywhere, exchange symmetric, invariant under
all simultaneous orthogonal rotations, globally essentially bounded, and
has the previously proved exponential H² tails. Its weak derivative family
and ordered weak Hessian are included in the statement. The existing decay
range is a ≥ 0 with a² < Z²/112. Attainment and the identification with the
actual spectral bottom are discharged by the earlier physical ground-branch
proofs, rather than assumed in this composition.

All new final declarations use only `propext`, `Classical.choice`, and
`Quot.sound`; no `sorry`, replacement mathematical axiom, or `native_decide`
is used. The local checks reuse pinned Mathlib and earlier project objects.
These sources are outside the running 392-source Colab snapshot and have
not yet completed an isolated dependency source rebuild. The compiler/core
bootstrap is not claimed. Independent proof agents were unavailable because
of their resource limit; the new chain has kernel checks and root review,
not an independent agent review.

The coefficient above is a separately proved, coarser Moser coefficient.
It does not verify the sharper constant in the earlier paper argument.
No novelty claim, new certified energy interval, solver implementation,
termination theorem, or bit-complexity claim is made here. Full Theorem T
remains unverified. The next active obligation is local Lipschitz regularity
through collisions, followed by the actual analytic and dictionary estimates.

Preservation: all work is new. Frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. The frozen local-regularity target is
`THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/RWA_THEOREM.md`, SHA-256
`d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`.
The frozen `RWA_REPORT.md` has SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
