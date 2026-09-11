> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# The scalar R18–R23 implication

Evidence category: a fully formalized conditional scalar implication. The
profile below is an arbitrary real family, not a definition of a physical
norm. Its application to the weighted Grushin PDE norms requires a separate
proof of the displayed hypotheses.

Let \(0<\rho\le1\), \(C,A\ge1\), and \(F,H_0\ge0\). Let
\(N_r(s)\) be nonnegative for \(0\le s\le\rho\), nonincreasing in
\(s\), and bounded by \(H_0\) there whenever \(r\le8\). Suppose that
for every \(r\ge9\), \(s\ge0\), and \(e>0\) with \(s+e\le\rho\),

\[
N_r(s+e)\le C\left[
FA^r r!+e^{-1}N_{r-1}(s)+e^{-2}N_{r-2}(s)
+\sum_{j=1}^{r} A^j\frac{r!}{(r-j)!}N_{r-j}(s)\right].
\]

Then, with \(B=2CA\) and \(S=F+H_0\), for every natural \(r\),

\[
N_r(\rho)\le 2BS\left(\frac{2B(r+1)}{\rho}\right)^r.
\]

In particular, \(S=0\) implies \(N_r(\rho)=0\) for every \(r\).
No division by \(S\) is used.

Fix \(\ell\ge1\) and put \(h=\rho/\ell\) and
\(d_r=h^rN_r((r+1)h)\) for \(r<\ell\). The falling-factorial
identity and its elementary power bound give, for \(j\le r<\ell\),

\[
h^j\frac{r!}{(r-j)!}\le\rho^j\le1,
\qquad h^r r!\le1.
\]

The base estimates imply \(d_r\le H_0\le S\) for \(r\le8\).
For larger \(r\), apply the raw recurrence at \(s=rh,e=h\).
The comparison \((r-j+1)h\le rh\) and the stated nonincreasing
profile hypothesis imply

\[
d_r\le C\left[SA^r+d_{r-1}+d_{r-2}
+\sum_{j=1}^{r}A^j d_{r-j}\right].
\]

All these \(d_q\) are nonnegative. Since \(A\ge1\), the first
two geometric terms dominate \(d_{r-1}+d_{r-2}\). Doubling the
whole geometric sum is a valid intermediate overestimate. For every
positive \(j\), \(2CA^j\le(2CA)^j=B^j\), and
\(CA^r\le B^{r+1}\). Therefore

\[
d_r\le SB^{r+1}+\sum_{j=1}^{r}B^j d_{r-j}.
\]

Strong induction uses the exact finite identity

\[
B^{r+1}+\sum_{j=1}^{r}B^j(2B)^{r-j+1}
=B^{r+1}(2^{r+1}-1)\le(2B)^{r+1}
\]

to obtain \(d_r\le S(2B)^{r+1}\). Choosing \(\ell=r+1\)
makes the evaluation point exactly \(\rho\); division only by the
positive number \(h^r\) proves the result, including \(r=0\).
The proof applies unchanged when \(S=0\).

The Lean root is
`TheoremT.Continuum.grushin_scalar_fixed_gap_bound` in
`lean/GrushinScalarFixedGapBound_v1.lean`. The recurrence definition uses
the finite index `j < r`, with loss `j+1`, exactly reindexing the displayed
sum. Its definition and the grid definition were read explicitly in
addition to auditing all expanded theorem statements and axiom dependencies.
All 25 declarations in the six new modules passed the approved v7 audit.

This discharges the scalar normalization and finite induction in
`audits/GRUSHIN_FACTORIAL_RECURRENCE_v1.md`, R18–R23, conditional on R18
and the stated base and monotonicity assumptions. It does not prove R18
for the actual weighted derivative norms, the later pointwise embedding,
the physical analytic approximation theorem, an executable solver, or a
complexity bound. No novelty claim is made.

The official pinned Lean 4.34.0-rc2 compiler and existing pinned dependency
objects were reused. This unit has no isolated source rebuild. Exact
sources, objects, build logs, and four strict receipts are bound in
`audits/GRUSHIN_SCALAR_FIXED_GAP_NORMALIZATION_CHECKPOINT_v1.json`.

Historical context is preserved at
`THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md`,
SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. No frozen or prior PASS artifact was
altered.
