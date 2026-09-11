> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact factor-Laplacian tests give genuine product weak H² derivatives

This is a fully formalized global implication for arbitrary finite-dimensional
real inner-product spaces `Y` and `T`. The ordinary Cartesian product keeps its
maximum norm and product Lebesgue measure. The codomain is complex, and the
inputs `f,w` are actual elements of `Lp ℂ 2 volume` on `Y × T`.

Choose any orthonormal bases `(bYᵢ)` and `(bTⱼ)` of the two factors and define,
using actual Fréchet derivatives,

\[
L_{Y,T}\varphi
=\sum_i D_{(bY_i,0)}^2\varphi
+\sum_j D_{(0,bT_j)}^2\varphi.
\]

Assume precisely the weak Laplacian equation

\[
\int \varphi w=\int (L_{Y,T}\varphi)f
\quad\text{for every real }\varphi\in C_c^\infty(Y\times T).
\]

Then there is a single family `d v` of actual complex L² elements, indexed by
all product directions `v`, such that, for every real smooth compact test,

\[
\int\varphi\,d_v f=-\int(D_v\varphi)f.
\]

For every ordered pair `v,q`, there is an actual L² element `e` satisfying

\[
\int\varphi e=-\int(D_q\varphi)d_v f.
\]

Thus the derivative conclusion concerns genuine weak first derivatives and
every ordered weak second derivative. The hypotheses do not supply these
derivatives, assume a density theorem, or assume the regularity conclusion.

The proof transports compact tests through the identity on points between
`Y × T` and `WithLp 2 (Y × T)`. The latter has the Euclidean norm, and Mathlib's
linear homeomorphism preserves exactly the relevant Lebesgue measures. The
new helper theorem proves the ordered second-derivative chain rule and
identifies `L_{Y,T}` with the pulled-back Euclidean Laplacian. Exact L² test
pairings transport without a Jacobian factor. The proved generic compact-test
converse then gives the actual tempered-distribution equation
`Δ (productEuclideanLift f) = productEuclideanLift w`. The existing generic
elliptic-gain theorem and the exact weak-test transport return the derivative
witnesses on the original product. A separate final theorem also displays the
tempered Laplacian as the two explicit factor-direction sums.

The exact final declarations are
`product_distribution_laplacian_of_compact_factor_tests`,
`product_factor_distribution_laplacian_of_compact_tests`, and
`product_weak_second_jets_of_compact_factor_laplacian_tests` in
`lean/ProductCompactLaplacianConverse_v1.lean`. The coordinate and integral
transport proofs are in `lean/ProductCompactTestTransport_v1.lean`.

Both sources compile in the declared Lean 4.34.0-rc2 environment. The associated
checkpoint records source/object hashes and a joint expanded-statement audit.
Only `propext`, `Classical.choice`, and `Quot.sound` occur in the complete axiom
reports. Development compilation reuses pinned library, prior-audit, and
continuation objects. These new modules are outside the sealed 671-target
desktop source-rebuild snapshot.

This result is global. It does not yet establish local weak Grushin gain,
partial-mollification commutation or convergence, quantitative local estimates,
analyticity, a certified algorithm, or full Theorem T. The existential L²
derivative witnesses are mathematical objects, not an executable selection
procedure. No novelty claim is made.

Preservation anchor: frozen `rwa_proof/RWA_THEOREM.md`, SHA-256
`d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. No frozen or prior successful source was
modified to obtain this result.
