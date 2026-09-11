> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual coordinate words control the Fréchet operator norm

The physical configuration used here is the existing
`Space κ = EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ`, with the product
maximum norm. Its coordinate directions are exactly the existing
`productCoordinateDirection`: four Y directions and `card κ` T directions.
There is no transfer to a different ambient norm.

For every vector x, the new coordinate-component function is its actual
Y or T component. The exact reconstruction

\[
x=\sum_j x_j e_j,\qquad |x_j|\le\|x\|
\]

is proved for these directions and this same norm. Applying reconstruction
in every slot of an actual continuous k-multilinear map T gives

\[
T(v_1,\ldots,v_k)=\sum_{a:\{1,\ldots,k\}\to I}
 \left(\prod_i(v_i)_{a(i)}\right)T(e_{a(1)},\ldots,e_{a(k)}).
\]

If every coordinate-tuple value has norm at most M, with M nonnegative,
each summand has norm at most \(M\prod_i\|v_i\|\). There are \(d^k\)
coordinate tuples, where \(d=|I|\). The actual continuous multilinear
operator-norm criterion therefore proves \(\|T\|\le d^k M\).
This generic lemma assumes only the explicit reconstruction and coordinate
magnitude inequalities; the physical specialization proves both.
The zero-order case is included: an empty tuple is the one term and
\(d^0=1\). No desired operator-norm estimate is assumed.

For an actual complex-valued function f which is C-infinity on an open
region Ω, the new array/list identity proves that the directional word
`List.ofFn a` is the value of the actual `iteratedFDeriv ℝ k f` on the
coordinate array a. It follows by induction from actual differentiation
of `iteratedFDeriv`; openness makes the induction identity valid in a
neighborhood of the evaluation point. Smoothness is an explicit hypothesis,
not supplied by this coordinate lemma.

Consequently, if all actual coordinate words w of length k satisfy
\(\|D_w f(x)\|\le M_k\), then

\[
\|D^k f(x)\|_{\mathrm{op}}\le(4+\operatorname{card}\kappa)^kM_k.
\]

For the physical seven-dimensional product κ = Fin 3, the factor is
exactly \(7^k\). This is a conservative dimension factor; no optimality
claim is made. Bounds
\(\|D_w f(x)\|\le CA^{|w|}|w|!\) for all words and x in Ω give

\[
\|D^k f(x)\|_{\mathrm{op}}\le C(7A)^k k!.
\]

Composing with the separately proved Taylor integral-remainder criterion
in `FactorialFrechetAnalytic_v1` gives actual real analyticity. For
C nonnegative and A positive, if every x in K has a ball of a common
radius δ > 0 contained in Ω, one radius

\[
r=\min\{\delta,(7A)^{-1}\}>0
\]

works at every x in K for the actual derivative Taylor series. The same
smoothness and word bounds also imply `AnalyticOnNhd ℝ f Ω` without a
common margin hypothesis. Constants and radius are chosen before the
point and order.

This unit does not prove smooth representatives for weak solutions, weak
jet identification with classical derivatives, the factorial word bounds
for a PDE solution, complex holomorphic extension, or an algorithm. It
supplies the precise coordinate-to-operator implication needed once those
mathematical premises are obtained. No novelty claim is made.

Five new modules contain eleven declarations. Exact source/object hashes,
compiler records, approved v7 expanded-statement and axiom audits, and the
focused independent review are bound in
`audits/PRODUCT_COORDINATE_FRECHET_BOUND_CHECKPOINT_v1.json`. Compilation
uses the official pinned Lean 4.34.0-rc2 compiler and existing pinned
library/prior-audit objects. This unit has no isolated dependency rebuild.

The frozen historical context is
`THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md`,
SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. Frozen and previous PASS artifacts
remain unchanged.
