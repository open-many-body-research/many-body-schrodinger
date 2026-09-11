> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Independent audit of the A/E finite experiment

**PROVEN (this session).** An independent exact-arithmetic audit passed 500 nonnegative distance moment cases, 465 independent overlap/weak-form Hamiltonian pairs for the 30-column E4 dictionary, and the scalar/provenance checks in all 17 certificate JSON files present when the audit ran (A2–A10 and E2–E9). Raw results are in `independent_audit.json`; the executable is `independent_audit.py`. This is an executable rational audit with a paper justification, not a Lean verification. No new approximation-rate theorem is claimed.

The independent moment calculation substitutes
\(r=x+z,s=y+z,u=x+y\), whose Jacobian is 2 and whose domain is the positive octant. For nonnegative powers it expands the three binomials and uses only
\(\int_0^\infty t^j e^{-ct}\,dt=j!/c^{j+1}\). It does not call the production angular recurrence. The independently evaluated Hamiltonian matrix uses the first-derivative quadratic form, including the two mixed radial-distance terms, rather than the production `h_action`. These exact checks cover unequal exponents 2, 4, and 8 in E4.

**PROVEN (this session).** The mixed-exponent formulas used by the certificates are correct. For columns \(e^{-\alpha(r+s)}P\) and \(e^{-\beta(r+s)}Q\), every product moment uses \(\kappa=\alpha+\beta\). Each individual Hamiltonian action retains its own exponent. The exact grouped-versus-pairwise check independently contracts the polynomial sums, but shares the basic moment kernel; it is not an independent proof of that kernel. The additional perimetric and weak-form checks above remove that shared dependency for the tested rational S and H entries.

For the inverse powers occurring in Q, a direct inspection of the existing angular recurrence found no discrepancy. Split at \(r=s\), set \(S=r+s,t=|r-s|/S,w=u/S\), and integrate \(w\) first. The angular weight is
\[
 [(1+t)^a(1-t)^b+(1-t)^a(1+t)^b]
 \begin{cases}(1-t^{c+1})/(c+1),&c\ge0,\\-\log t,&c=-1.\end{cases}
\]
When \(a=-1\), its rational prefactor equals
\([(1-t)^{b+1}+(1+t)^{b+1}]/(1-t^2)\), exactly the even-binomial branch in the implementation. The remaining elementary integrals are the stated rational/log(2)/pi-squared recurrence. This is a paper check of the full formula; the new executable audit does not independently recompute every inverse-power Q moment by another numerical integrator.

**PROVEN (this session).** The additive optimization check has the right direction. Interval LDL proves both \(S>0\) and \(W-\lambda_*S>0\), with \(W=Q+10H+25S+\tau I\), \(\tau=2^{-160}>0\). Therefore \(\lambda_*<\lambda_{\min}(W,S)\). If the interval trial quotient is \([q_-,q_+]\), the code sets \(\lambda_*=q_- -\delta/2\) and checks \(q_+-\lambda_*\le\delta=10^{-16}\) exactly. Thus the selected rational trial is within additive \(\delta\) of the minimum of this positive regularized fixed-shift pencil. The result is not merely a small stationary residual or a relative-tolerance claim.

**PROVEN (this session).** Conditional only on the already established helium continuum domain and separator facts, the new scalar residual enclosures are correct. For normalized trial \(\phi\), mean \(m\), variance \(v\), and its own Temple energy enclosure \([\ell,u]\),
\[
 \|(H-E)\phi\|^2=v+(m-E)^2
 \in[v_-,v_++(m-\ell)^2].
\]
The code uses \(E\le m\), rather than an external numerical reference. This is the ground-energy residual squared; it is not a separately established full graph-norm distance to a normalized eigenvector. For the physical fixed-shift objective \(J=\|(H+5)\phi\|^2\), \(\ell+5>0\) gives
\[
 J-(E+5)^2\in
 [\max(0,J_--(u+5)^2),\ J_+-(\ell+5)^2].
\]
The clipping to zero uses the existing lower spectral bound \(H\ge-4\), so that the bottom of \((H+5)^2\) is \((E+5)^2\). All audited certificates meet the strict filter \(m\le-11/4\). Their decimal endpoint formatting is rational outward rounding to 24 places.

**PROVEN (this session).** Every audited trial hash, matrix hash, code hash, and certificate SHA-256 sidecar matches its corresponding current file. No floating-point value enters a load-bearing certificate comparison. Floating-point wall-time metadata are strings and are irrelevant to the proof. This audit ran on the same Mac; it is an independent implementation/review check, not evidence of independent-host recomputation.

**PROVEN (this session).** The basic effective-dictionary argument for E survives review. In
\[
 E_n=\sum_{j=0}^{\lfloor n/2\rfloor}e^{-2\,2^j(r+s)}\mathcal P_{n-2j}^{\rm sym},
\]
there are \(O(n^4)\) columns, exponents have \(O(n)\) bits, and exact dyadic diagonal scaling leaves squared norms in \([1/2,2]\). Each entry of S and H is rational of polynomial bit height: degrees are \(O(n)\), exponent sums have \(O(n)\) bits, factorials have \(O(n\log(n+2))\) bits, and all finite expansions contain polynomially many terms. Q has three rational coefficients of polynomial bit height in the fixed field \(\mathbb Q+\mathbb Q\log2+\mathbb Q\pi^2\).

Distinct-exponent exponential-polynomial independence proves S is positive definite: fix the two angular ratios, apply univariate exponential-polynomial independence in \(r+s\), then use polynomial independence on the open ratio triangle. If every reduced entry denominator of an m-by-m S has at most B bits, the product P of those denominators is at most \(2^{m^2B}\). Since \(\det S\) is a positive rational with denominator dividing P,
\[
 \det S\ge 2^{-m^2B},\qquad
 \lambda_{\min}(S)\ge
 2^{-m^2B}(2m)^{-(m-1)},
\]
using \(\operatorname{tr}S\le2m\). Hence this crude Gram conditioning bound and normalized coefficient bound require only polynomially many bits in n. This argument does not need a lower bound for a nonzero expression involving log(2) or pi-squared, because S is rational. It does not supply RATE or explicit optimized complexity constants.

**OPEN.** The fixed finite tolerance and regularization used in this experiment are not an asymptotic algorithm. A future theorem must schedule both as functions of n and the requested accuracy; it must quantify the preceding height bounds and the cost of all operations. Most importantly, neither the finite certificates nor the Gram argument proves approximation at \(\exp(-c n^\alpha)\) in the ground-energy residual or graph norm. That is the remaining analytic obligation. No defect found in this bounded audit invalidates the E finite-instance data or the proposed use of those data to select the next RATE conjecture.

Reproduction: `/usr/bin/python3 rate_decision/independent_audit.py`. The script intentionally audits every completed A/E certificate currently present, so its output list and result hash may grow when a later certificate is added.
