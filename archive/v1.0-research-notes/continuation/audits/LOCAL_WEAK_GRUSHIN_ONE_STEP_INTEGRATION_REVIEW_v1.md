> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Focused review of the actual one-step Grushin gain

No defect was found in the completed integration. The final theorem derives
actual weak derivatives from the local compact-test equation; it no longer
assumes local or global weak H² regularity of the original input.

For fixed (c>0), open (Omega), and smooth compact (chi) supported inside

(Omega),

the raw-data theorem chooses compact (K\subseteq\Omega) and (C\ge0) before
the locally L² input and source. Its output is an actual L² representative of

(chi f),

with first weak derivatives in all (y,t) coordinate directions and all ordered
second weak (yy) derivatives. The bounds use the exact finite quantities

\[
 F=\int_K|f|^2,\qquad M=\int_K|h|^2,
\]

and preserve the coefficients (2,3/4,1/(16c),3/2) established by the compact
anisotropic estimate. Neither unweighted mixed second derivatives nor second
spectator derivatives are claimed.

The main proof chooses the interior test region and cutoff constant before
regularization. Spectator mollification produces actual L² contractions and
strong L² convergence. On one eventual tail, the mollified functions satisfy
the PDE for every interior test and have local weak H² jets. The previously
reviewed cutoff theorem constructs actual compact weak H² outputs with bounds
uniform in the smoothing index; it does not assume those bounds.

The eventual-tail limiting theorem discards finitely many initial indices and
uses genuine weak derivative witnesses only on the good tail. Strong convergence
of the input, together with bounded finite families of derivative outputs,
constructs the limit derivatives. It does not assume convergence of the
derivatives or their existence at the limit. Separate finite-family bounds are
identified with one common derivative family by weak derivative uniqueness.
Noncomputable selections are mathematical existence witnesses, not an algorithm.

The raw-data wrapper first extends the input and source from a fixed compact
region into global L² using their indicators. It differentiates only compact
tests, whose Grushin images retain the same support. Therefore no derivative of
an indicator is used. Its exact L² norm identities transfer the global theorem's
bounds into the restricted quantities (F,M). Both (K) and (C) precede the
raw inputs in the fully expanded theorem type.

A parallel focused review checked the regularization stage and its support
quantifiers. The spectator jets are constructed by convolving the L² input
with actual derivatives of the compact smooth kernel. The elliptic rewrite is

\[
 \Delta_{y,t}f_n=-h_n+(1-c|y|^2)\sum_j\partial_{t_j}^2f_n.
\]

The coefficient depends only on (y), and the spectator integrations by parts
produce no coefficient derivatives. The right-hand side is proved L² on each
compact region before applying the local elliptic theorem. No global L² bound
for that weighted right-hand side is assumed. The intermediate spectator
derivative norms may depend on the smoothing index; the later energy argument
supplies the uniform bounds actually needed for passage to the limit.

The support threshold is selected from compact containment before the test
function. Thus the conclusion is “eventually in (n), for every interior test,”
with no invalid exchange of these quantifiers. The ordinary product norm gives

(\|(0,s)\|=\|s\|),

as used by the translation estimates. Preliminary regularization accepts any
real (c); strict positivity enters only the coercive estimate and division.

This review rehashed ten directly inspected PASS source/object pairs and nine
strict receipts, covering thirteen declarations in that selected source set.
Complete type and axiom records were reparsed, with no ellipses and only
`propext`, `Classical.choice`, and `Quot.sound`. The two final expanded types
contain no `ProductLocalWeakH2On` premise. Exact fingerprints are in
`LOCAL_WEAK_GRUSHIN_ONE_STEP_INTEGRATION_REVIEW_v1.json`, SHA-256
`1429c3f7ae315967dc6c19eb261a32ab714af24e7332cdc8eeb9ea55f51515e0`.
The separate regularization review and its anchors are attached append-only.

No source was changed and no compiler was run for this review. Earlier cutoff
and foundational audits were reused. Potential/physical KS application,
repeated derivative gains, factorial analytic estimates, approximation, and
certified computation remain separate obligations.
