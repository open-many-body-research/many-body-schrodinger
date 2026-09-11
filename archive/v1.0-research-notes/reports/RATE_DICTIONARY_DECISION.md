> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Which RATE lemma should we try to prove next?

Decision experiment, 9 September 2026. This report concerns the atomic two-electron problem in `TWO_ELECTRON_THEOREM.md`. Theorem T remains **OPEN**. No new continuum approximation theorem or Lean theorem is claimed.

## Fixed problem, objective, and status conventions

All numerical experiments use helium, \(Z=2\), with the unrestricted operator

\[
H=-\tfrac12(\Delta_1+\Delta_2)-2/r-2/s+1/u,
\quad r=|x_1|, s=|x_2|, u=|x_1-x_2|.
\]

The spatial functions below are symmetric under \(r\leftrightarrow s\); multiplication by the normalized antisymmetric spin singlet gives fermionic trials in \(D(H)=H^2(\mathbb R^6;\mathbb C^4)\cap\mathcal H_-\). The scalar products omit their common angular constant only. Every reported \(Q_{ij}\) is ⟨Hφ_i,Hφ_j⟩ for the continuum action, not the square of a projected Hamiltonian.

**PROVEN (existing paper):** the prior report supplies \(L=-4, U=-11/4, \beta=-5/2\), the operator-domain facts for ordinary distance polynomials and conforming hp lifts, and the continuum Temple argument. Its Theorem C rules out the requested fast asymptotic graph rate for every *fixed finite* positive exponential set with nonnegative distance powers. The precise exponent 72 in that obstruction is not a fitted exponent.

Selection uses only the corrected fixed shift \(\sigma=-5\):

\[
J_\tau(c)=\frac{c^T(Q+10A+25G+\tau I)c}{c^TGc},\qquad \tau>0.
\]

The equivalent reciprocal maximization is used where numerically more stable. Candidate coefficients are rationalized before certification. The acceptance test is \(m=\langle H\rangle\le-11/4\). A near-eigenvalue shift and global variance optimization are absent. Published helium digits, where present in exploratory diagnostics, are not selection, acceptance, or certificate inputs.

**EMPIRICAL** means finite arithmetic screening, fits, timing, or a scientific judgment about the next proof target. **PROVEN (this session)** means the elementary finite calculations explained here or the exact rational interval certificate checked by Python; it does not mean Lean verified. **OPEN** marks missing analytic/effective bounds. **REFUTED** is reserved for an actual obstruction, not an unsuccessful pilot.

## Phase 0: exact dictionaries and the domain/certification gate

Let \(\mathcal P_d\) be the symmetric nonnegative-power distance polynomials of total degree at most \(d\), with \(\mathcal P_d=\{0\}\) for \(d<0\). A generator is
\[
P_{ihk}=\frac{(r^is^h+r^hs^i)u^k}{(i+h+k)!},\quad i\ge h\ge0, i+h+k\le d,
\]
using one copy rather than two when \(i=h\). Define \(a_d=\dim\mathcal P_d\). For \(d=2q,2q+1\), respectively,
\[
a_{2q}=\frac{(q+1)(q+2)(4q+3)}6,\qquad
a_{2q+1}=\frac{(q+1)(q+2)(4q+9)}6.
\]

| Candidate | Exact dictionary | Domain | Moments and implementation | Size / parameter heights | Obstruction / effort |
|---|---|---|---|---|---|
| A, control | \(e^{-2(r+s)}\mathcal P_n\) | **PROVEN (existing paper)** | Existing exact \(G,A\in\mathbb Q\), \(Q\in\mathbb Q+\mathbb Q\log2+\mathbb Q\pi^2\); fixed-shift driver added | \(a_n=O(n^3)\); polynomial rational heights | Fast RATE **REFUTED** by Theorem C; minimal implementation |
| B, quadratic Fock log | \(e^{-2(r+s)}[\mathcal P_n+q\log R\,\mathcal P_{n-2}]\), \(q=(r^2+s^2-u^2)/2, R=r^2+s^2\) | **PROVEN (this session)**, elementary check below | Finite radial log moments and one-dimensional angular integrals; new screening evaluator | \(a_n+a_{n-2}=O(n^3)\); fixed rational parameters | Physical full-eigenfunction approximation and conditioning **OPEN**; medium new moment work |
| C, Schwartz F | \(e^{-S}S^\ell(U/S)^m(T/S)^{2j}(\log S)^h\), \(h=0,1, \ell,m,j\ge0, \ell+m+2j\le n\), \(S=r+s,T=r-s,U=u\) | **PROVEN (this session)**, including degree-zero logarithms | Exact angular recurrence with radial log moments in a larger explicit constant algebra; screening/certification extension | \(2\sum_{j=0}^{\lfloor n/2\rfloor}\binom{n-2j+2}{2}=O(n^3)\); polynomial rational generator heights | Physical graph RATE and quantitative Gram control **OPEN**; medium extension |
| D, full tensor hp | Defined precisely below on dyadic tensor cells; globally \(C^1\), degree \(p_n=3+\lfloor n/3\rfloor^2\) | **PROVEN (existing paper)**, applied to the explicit generator | Rational \(G,A\); rational-integrand \(Q\); implemented Duffy screening, explicit rational quadrature route | \(O(n^9)\); polynomial knot/basis heights | LPWA, graph interpolation and exterior/tail bridge **OPEN**; highest implementation effort |
| E, expanding exponents | \(\sum_{j=0}^{\lfloor n/2\rfloor}e^{-2^{j+1}(r+s)}\mathcal P_{n-2j}\) | **PROVEN (existing paper)** applied termwise | Existing moment field unchanged; complete exact/interval implementation | \(\sum_j a_{n-2j}=O(n^4)\); largest exponent bit length \(\lfloor n/2\rfloor+2\) | Theorem C does not cover an expanding set; direct graph approximation **OPEN**; small exact-code extension |

Here is the exact D generator. On each axis take breakpoints \(\{0\}\cup\{2^j:-n\le j\le n+1\}\), endpoint knot multiplicity \(p_n+1\), and interior multiplicity \(p_n-1\). Use the resulting rational B-splines of degree \(p_n\), deleting the last two functions so that value and first derivative vanish at the outer endpoint. Extend by zero. Take the tensor products and retain one symmetric (a,b) combination per exchange orbit. No boundary value is prescribed on a physical octant face. The spaces are nested by knot insertion, degree elevation, and extension of the outer zero region. There are \(O(n^3)\) one-dimensional generators and \(O(n^9)\) tensor generators. The measured dimensions are actual independent B-spline dimensions, not merely a count of redundant columns.

To obtain a cheaper but explicitly distinct hp trend, we also screen **D-shell**: compact \(C^1\) radial splines in \(t=a+b+c\), degree \(n+3\), breakpoints \(\{0\}\cup\{2^j:-n\le j\le n+2\}\), multiplied by \(c^j(a-b)^{2k}\) with \(j+2k\le n\). This is a genuine conforming piecewise-polynomial family on simplex shells, of size \(O(n^4)\). It is not the tensor family and is not substituted for it in a RATE claim.

**PROVEN (this session), finite domain checks.** For B, \(q=O(\rho^2)\), \(R\asymp\rho^2\) in six spatial dimensions, so derivatives of \(q\log R\) of orders 0,1,2 have orders \(\rho^2\log\rho,\rho\log\rho,1+|\log\rho|\). Their relevant squares are locally integrable. Distance cusps introduce at most inverse pair distances in the Hessian, square integrable in transverse dimension three. Exponential decay controls infinity. Products and finite sums retain \(H^2\), and Hardy controls Coulomb multiplication. For C, each generator is homogeneous of degree \(\ell\) times a bounded angular function and at most one radial logarithm. The \(S\) denominator vanishes only at the six-dimensional origin; two derivatives there have radial size \(\rho^{\ell-2}(1+|\log\rho|)\), whose squared radial integral is bounded by a constant times \(\int_0^1\rho^{2\ell+1}(1+|\log\rho|)^2d\rho<\infty\). At nonzero pair collisions only the usual distance-cusp factors occur. Standard shrinking-boundary integration by parts gives these derivatives distributionally; it introduces no point or interface delta. Thus even the \(\ell=0\), \(\log S\) functions are admissible. No silently removed terms are needed for domain membership.

The C indexing and decay are those of Schwartz, equation (0.3), [math-ph/0605018](https://arxiv.org/abs/math-ph/0605018): its \(k=2\) means \(e^{-S}\), not \(e^{-2S}\). The entire displayed dictionary is used. The earlier [physics/0208004](https://arxiv.org/abs/physics/0208004) low-log omissions are not silently mixed into this definition. B uses the actual quadratic scalar product in the Fournais factor, [math-ph/0312060](https://arxiv.org/abs/math-ph/0312060), DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6). Depth two is not run: \(H^2\)-admissibility of its square is easy, but a verified nonzero *physical* quartic log-square coefficient was not established by the available \(C^{1,1}\) factorization. That factorization permits cancellation by the remainder.

No family fails the finite domain gate. The analytic RATE is open for B–E. Where a certifier is not implemented, cheap screening is explicitly separated from a certified result; the concrete moment routes below explain why screening is meaningful, and no expensive certificate run is based on an unspecified integral oracle.

## Moment classes and certification obligations

**PROVEN (existing paper), instantiated this session:** for A/E, mixed exponent products use \(\kappa=\alpha_i+\alpha_j>0\). All required integrals are
\[
M_{abc}(\kappa)=\int_{|r-s|\le u\le r+s}e^{-\kappa(r+s)}r^as^bu^c\,dr\,ds\,du,
\quad a,b,c\ge-1, a+b+c>-3.
\]
The radial factor is \((a+b+c+2)!/\kappa^{a+b+c+3}\); the angular recurrence is unchanged. With its powers of two included, the full field remains \(\mathbb Q+\mathbb Q\log2+\mathbb Q\pi^2\). Both exponent-dependent \(H\)-actions are evaluated before taking a mixed inner product.

For C the extension is
\[
\int_\triangle e^{-\kappa S}r^as^bu^cS^d(\log S)^h\,dr\,ds\,du,
\qquad h\le2.
\]
After the same angular integration, let \(\nu=a+b+c+d+2\ge1\). The three radial factors are
\[
R_{\nu,0}=\nu!/\kappa^{\nu+1},\quad
R_{\nu,1}=R_{\nu,0}(H_\nu-\gamma-\log\kappa),
\]
\[
R_{\nu,2}=R_{\nu,0}[(H_\nu-\gamma-\log\kappa)^2+\pi^2/6-H_\nu^{(2)}].
\]
For this dictionary \(\kappa=2\), yielding the algebra \(\mathbb Q[\gamma,\log2,\pi^2]\), with bounded logarithmic degree. This is larger than the old three-component vector field. One can alternatively bound the base radial log integrals directly and generate higher moments by integration by parts. For example, \(\gamma=-\int_0^\infty e^{-t}\log t\,dt\). On \([0,T]\), integrate the Taylor polynomial of \(e^{-t}\) exactly against \(\log t\); each term is \(T^{k+1}[\log T/(k+1)-1/(k+1)^2]\). A remainder bound is
\[
\frac{T^{K+2}(\log T/(K+2)-1/(K+2)^2)+2/(K+2)^2}{(K+1)!},
\]
and for \(T\ge1\) the tail is at most \((T+1)2^{-T}\). Dyadic \(T=O(p)\) and sufficiently large \(K=O(p)\) give a rational \(p\)-bit route without using a floating gamma value as a certificate.

For B the new class is
\[
\int_\triangle e^{-4(r+s)}r^as^bu^c(r^2+s^2)^{-d}
[\log(r^2+s^2)]^h\,dr\,ds\,du.
\]
Set \(S=r+s, t=|r-s|/S\). Then \(R=S^2(1+t^2)/2\); the radial part uses positive-integer gamma derivatives and the remaining one-dimensional angular part contains rational factors, \(\log((1+t^2)/2)\), and possibly \(-\log t\). Endpoint cancellations must be grouped before bounding. This is a direct certified quadrature problem, not an assertion that the old moment field suffices. A finite quadrature extension is distinct from the still-open polynomial conditioning and physical RATE theorem.

For D, with \(w=(a+b)(a+c)(b+c)\), cellwise \(H\phi_i=P_i/w\), hence
\[
Q_{ij}=\int_{\rm cell}\frac{P_iP_j}{w}\,da\,db\,dc.
\]
On an origin cube split into six coordinate orderings. On one sector \(a=h\rho,b=h\rho t,c=h\rho tv\), the denominator and Jacobian give \([\rho(1+t)(1+v)(1+tv)]^{-1}\). Since each \(P_i\) vanishes to order at least two, the radial singularity cancels. Axis cells use a two-dimensional Duffy map. Remaining denominators are separated from zero on each rescaled geometric cell. Expand each reciprocal about a rational midpoint: if \(|1-D/D_0|\le1/2\), the geometric tail after \(K\) terms is at most \(2^{1-K}/D_0\). The retained polynomial integrates rationally. This gives a specific constant-tracking route; a complete global generator/quadrature bit bound is **OPEN**, not inferred merely from computability.

## Phase 1: executed screening

**EMPIRICAL.** All five candidates were executed, plus the separately labeled shell hp prototype. The full raw screening table records every level's native index, dimension, mean, Rayleigh residual, shifted objective, conditioning diagnostic and wall time. A/E used Decimal80 (E10 repeated at120 digits), C Decimal90 (C8 repeated at120), and B 50/70 digits. D used float64 selection followed by independent 50–70-digit evaluations of frozen rational witnesses and quadrature refinements. Thus D's precise moments were audited at high precision, but its optimizer itself was not rerun as a high-precision minimizer; no additive optimality or continuum certificate is claimed for D.

Regularization was positive throughout: A/C/E used \(2^{-160}\), B \(2^{-120}\), and D \(2^{-80}\). These values refer to the reduced scalar-product matrices with their common angular factor omitted, equivalently a fixed overall rescaling of each dictionary. If using the unscaled spatial columns, multiply the regularizer by the omitted \(8\pi^2\) (A/B/C/E) or \(16\pi^2\) \(D\). This leaves every unregularized physical quotient unchanged. Only certified survivors claim additive solve error at most \(10^{-16}\); small exploratory pencil residuals alone do not prove it.

| Family | largest native index | dimension | mean | sqrt(variance) | Temple width | precision / condition diagnostic |
|---|---:|---:|---:|---:|---:|---|
| A | 10 | 161 | -2.903724144385 | 0.003210231 | 2.55263e-05 | 80 Decimal digits; 5.99e+11 |
| B | 8 | 145 | -2.903724291068 | 0.002017891 | 1.00858e-05 | 70 mpmath/Decimal digits; 5.44e+10 |
| C | 8 | 190 | -2.903724376528 | 8.991999e-05 | 2.002754e-08 | 90 Decimal digits; 3.11e+16 |
| D-shell | 6 | 1920 | -2.903721380187 | 0.007288545 | 0.000131583 | float64 selection; 50–70 digit selected-witness audits; 2.87e+12 |
| D-tensor | 3 | 936 | -2.901132822541 | 0.2485234 | 0.1539737 | float64 selection; 50–60 digit selected-witness audits; 8.64e+03 |
| E | 10 | 336 | -2.903724377006 | 5.749056e-05 | 8.186686e-09 | 80 Decimal digits; 4.61e+13 |

[Every screening row](rate_decision/screening_table.md); [machine-readable fits and provenance](rate_decision/all_rate_diagnostics.json).

The A/B/C/E condition numbers in that table are explicitly **LDL pivot-ratio proxies**, not spectral condition numbers. D reports numerical spectral Gram conditions. They are not interchangeable scores. Full tensor hp uses positive plotting index \(N=n+1\) for raw stages \(n=0,1,2\); all three tested polynomial degrees are cubic. Its first stage and the shell family's first stage fail the strict mean filter. The remaining displayed hp levels pass it, but passing the filter does not certify their moments.

The comparisons that matter are not equal-order comparisons. C8 has 190 functions and width about \(2.003\times10^{-8}\), versus E8's175 functions and \(3.622\times10^{-7}\): roughly 18 times narrower. C8 is also narrower than E9 with 245 functions. E10 uses 336 functions to reach \(8.187\times10^{-9}\). E8 nevertheless improves about 70 times over A10 at similar dimension (175 versus161). B8 uses 145 functions and reaches only \(1.009\times10^{-5}\). The full tensor hp pilot is substantially more expensive in dimension at these early stages; three h-dominated cubic stages cannot estimate its asymptotic hp exponent.

The accuracy cross-checks support using these pilot values for a decision: E10's80/120-digit shifted objectives differ by about \(1.94\times10^{-69}\); C8's90/120-digit objectives by about \(1.48\times10^{-82}\). B's50/70-digit width repeats differ by at most \(2.58\times10^{-47}\). The independently transformed B moments and Cartesian action checks are high-precision *empirical* checks. C's100 Cartesian action checks are exact symbolic comparisons, while its 13 quadrature checks are empirical. Full tensor D at its second stage agrees across q12/q20 high-precision quadrature to roughly \(10^{-15}\) in objective; its third-stage q20/q28 residual changes by about \(4\times10^{-12}\). The shell family's order-6 residual changes only about \(1.6\times10^{-9}\) under the high-precision witness audit. None of these precision comparisons is a RATE proof.

Detailed finite-family notes: [B](rate_decision/fock/NOTES.md), [C](rate_decision/schwartz/NOTES.md), [D](rate_decision/hp/HP_NOTES.md).


## Phase 2: survivor certificates

**PROVEN (this session).** There are 24 new rational interval certificates: A2–A10, E2–E10, and C3–C8. Every certificate passes the strict mean filter and an interval-LDL proof of additive optimality within \(10^{-16}\) for its positive regularized fixed-shift pencil. The raw coefficients remain rational JSON. B and D were not selected for certification; their reported widths are exploratory only.

The two log constants in the old field use rational atanh-series bounds for \(\log2\) and Machin alternating-arctangent bounds for \(\pi\). C additionally uses the rational integrated-Taylor gamma enclosure in `gamma_interval.py`. Its implemented tail is the stronger \((T+1)(3/8)^T\), using \(e>8/3\). All arithmetic that feeds an endpoint is Fraction arithmetic with outward dyadic rounding. Decimal formatting to24 places is itself an exact outward rational operation.

The strongest certificates from each retained family are below. **Every integer in this table is a numerator over the common denominator \(D=10^{24}\).** Thus this is an exact rational table, not floating-point output.

| Family | n,m | D ell | D u | D width |
|---|---|---:|---:|---:|
| A | 10,161 | -2903749670686108980841683 | -2903724144384985331494865 | 25526301123649346818 |
| C | 8,190 | -2903724396556005728924298 | -2903724376528468111212759 | 20027537617711539 |
| E | 10,336 | -2903724385192751581540207 | -2903724377006065467379698 | 8186686114160509 |

[All 24 exact endpoint rows with individual certificate links](rate_decision/certificate_table.md); [final scalar/hash audit](rate_decision/artifact_audit.json).

The physically relevant residual is kept separate from energy width. For the normalized selected trial, write \(v=\|(H-m)\phi\|^2\), \(E=\inf\operatorname{spec}H\), and use its *own* Temple interval \([\ell,u]\). Then
\[
\|(H-E)\phi\|^2=v+(m-E)^2\in[v_-,v_++(m_+-\ell)^2].
\]
Here \(m_+=m\) for A/E and the interval upper mean for C. For the physical unregularized objective \(J=\|(H+5)\phi\|^2\), \(\ell+5>0\) gives
\[
J-(E+5)^2\in[\max(0,J_--(u+5)^2),J_+-(\ell+5)^2].
\]
This uses no external helium reference. The following are conservative rational enclosures, again with denominator \(D=10^{24}\); the JSON retains tighter original interval endpoints.

| Family | D·mean interval | D·variance interval | D·ground-residual-squared interval | D·shifted-excess interval |
|---|---|---|---|---|
| A | [-2903724144384985331494866, -2903724144384985331494865] | [10305584080458822199, 10305584080458822200] | [10305584080458822199, 10306235672507877422] | [10305584080458822198, 117325269945738856667] |
| C | [-2903724376528468111212760, -2903724376528468111212759] | [8085605138111031, 8085605138111032] | [8085605138111031, 8085605539213295] | [8085605138111028, 92052082549344395] |
| E | [-2903724377006065467379699, -2903724377006065467379698] | [3305164751183657, 3305164751183658] | [3305164751183657, 3305164818205488] | [3305164751183656, 37628265752597056] |

E10's512-bit interval-LDL trial did not prove a positive pivot at row280/336. That failed log is preserved; no certificate was emitted from it. The *same* rational input passed at1024 bits in about353 seconds. C8 passed at512 bits in about153 seconds. These are certified finite optimization/energy facts and empirical runtime facts, respectively.

The independent audit used an alternative perimetric expansion for 500 rational moments and a first-derivative weak form for all 465 overlap/Hamiltonian pairs in E4. Grouped versus pairwise contraction was checked exactly for every survivor trial. The latter check shares the basic moment kernel; it is not an independent implementation of every inverse-power Q moment. C additionally received exact Cartesian derivative comparisons for 100 basis terms and an elementary independent derivation of the radial log-square moments. The report does not convert these bounded audits into a machine-verified continuum theorem.

[Independent audit details](rate_decision/INDEPENDENT_AUDIT.md).

Windows re-evaluated the full E9 and E10 trial moments at1024 and1536 bits under Python3.13.0/AMD64, recording host <host-redacted>. Their reported rational energy endpoints equal the Mac endpoints exactly, and their variance intervals nest. This second-host E check does not repeat the finite-pencil LDL; its scope is explicitly recorded. Windows also repeated the complete 512-bit C8 certificate, including its additive interval-LDL proof, using only standard-library Python. Its exact energy endpoints agree with the Mac certificate. All returned results are canonical local files in `helium/rate_decision_windows/`. No Colab job or GPU arithmetic contributed to a certificate in this session.

[Windows recomputations and logs](helium/rate_decision_windows).


## Phase 3: rate diagnostics and their limits

**EMPIRICAL.** All fits use least squares in log error. Power, exponential, and stretched exponential models were compared; the stretched scan is \(\alpha=0.05,0.06,\ldots,1\). Full-range, trailing-five, trailing-four, last-two holdout predictions, and successive effective slopes are saved for both native index and dimension. The cross-family metric is \(\sqrt v\), the Rayleigh residual, rather than a published-energy residual. Survivor JSONs separately enclose the true ground residual; for their small widths its square differs from \(v\) by at most the squared Temple error. Native-index conclusions therefore have a checked bridge to the requested residual on these finite instances.

| Family | full / trailing5 / trailing4 preferred alpha vs n | full exponential c | last-two exponential predicted / observed residual | interpretation |
|---|---|---:|---|---|
| A | 0.12 / 0.23 / 0.2 | 0.3912 | 0.690, 0.561 | False-positive warning: Theorem C excludes every fast asymptotic rate here. |
| B | 0.07 / 0.3 / 0.6 | 0.6009 | 0.662, 0.464 | Exponent drifts; power fits predict held-out data substantially better. |
| C | 0.94 / 0.96 / 0.89 | 1.2423 | 0.949, 0.836 | Near-exponential finite range, but no asymptotic theorem. |
| D-shell | 1.0 / 1.0 / 1.0 | 1.0934 | 1.347, 1.788 | Fast finite trend with large dimensions; slopes still move. |
| D-tensor | 0.05 / — / — | 0.9223 | — | Only three cubic stages: an asymptotic fit is uninformative. |
| E | 1.0 / 1.0 / 1.0 | 0.9170 | 1.043, 1.126 | Stable near-exponential finite range; RATE remains OPEN. |

[All model residual sums, dimension fits and predictive checks](rate_decision/fit_table.md); [raw local slopes and full fits](rate_decision/all_rate_diagnostics.json).

E's residual-vs-dimension stretched exponent is about 0.29 on the full range and 0.31 on trailing windows. C's finite-dimension transform differs because its dimension is \(O(n^3)\), versus E's \(O(n^4)\). Neither measured exponent should be read as the native theorem's exponent. The full tensor D fits use \(N=n+1>0\); the fact that all pilot degrees are3 prevents extrapolating the \(p\sim N^2\) regime. Its accepted widths supply only two points, so the requested multi-model/holdout comparison is honestly marked insufficient. D-shell has six points and is fitted separately.

For E, the local power exponent grows from about 4 to about 9 as n increases, while the local exponential slope stays near0.9–1; C has a similar finite-range preference for exponential/stretched models. B and A have much more stable effective power exponents. The fitted small positive stretched alpha for A, despite the proved obstruction, is an internal demonstration that a winning three-parameter curve is not evidence of an asymptotic theorem. Scanned alpha near0 also approaches a reparameterized power curve and is poorly identifiable from short windows.

Temple width is approximately \(v/(\beta-m)\). A near-constant gap makes the *log-width decay coefficient* roughly twice the residual's, not the native stretched exponent alpha. No width plot by itself establishes the target graph RATE.


## Phase 4: the next proof target

**EMPIRICAL decision:** choose **E, the deterministic expanding dyadic exponent dictionary**, for the next RATE proof/refutation session. C is the strongest numerical competitor and wins the tested comparison at similar dimensions. The reason to choose E is the combination of certified rapid finite-range decay and an elementary route through every effective-dictionary requirement except physical approximation. This is a decision about where to spend proof effort; it is not a theorem that E ultimately converges faster than C or D.

The following scores are **EMPIRICAL judgments**, not probabilities or theorem counts: 0 = adverse evidence or a proved obstruction; 1 = a substantial unresolved bridge; 2 = a concrete promising route; 3 = strongest evidence or a finite mechanism established here. They are intentionally not summed into a fictitious objective ranking.

| Criterion | A | B, log depth 1 | C, full F | D, full tensor hp | E, expanding |
|---|---:|---:|---:|---:|---:|
| A. Finite residual/width decay | 0 | 1 | 3 | 1 | 2 |
| B. Compatibility with physical singularities | 0 | 2 | 2 | 3 | 2 |
| C. Credible direct approximation proof route | 0 | 1 | 1 | 2 | 2 |
| D. Operator-domain conformity | 3 | 3 | 3 | 3 | 3 |
| E. Polynomial-precision moment route | 3 | 2 | 3 | 2 | 3 |
| F. Polynomial size, with practical exponent considered | 3 | 3 | 3 | 2 | 3 |
| G. Polynomial parameter description | 3 | 3 | 3 | 3 | 3 |
| H. Quantitative coefficient / conditioning route | 3 | 1 | 1 | 2 | 3 |
| I. Status of known obstruction | 0 | 2 | 2 | 2 | 2 |

An obstruction score of 2 means that Theorem C does not apply, not that all obstructions have been ruled out. D's modest experimental score records its limited pilot; it does not disprove an hp rate. C's score of 1 for conditioning records a missing all-order bound, despite successful finite LDL certificates.

**PROVEN (this session), elementary effective-dictionary checks for E.** The exponents and degree allocation are deterministic, with no continuous optimization of exponent locations. Each generator is dyadically rescaled so that its reduced norm squared is in [1/2,2]. Degrees are (O\(n\)), exponents and exponent sums have (O\(n\)) bits, factorials have \(O(n\log(n+2))\) bits, and every finite polynomial expansion has polynomially many terms. Thus the rational coefficients of (G,A,Q) in the fixed moment field have polynomial bit height. Values such as the high kinetic-energy matrix entries can grow exponentially in \(n\); their *bit lengths* remain polynomial.

The Gram matrix is rational and positive definite. To see independence, fix an interior pair of angular ratios and vary \(S=r+s>0\). Distinct exponent polynomial sums are linearly independent as functions of \(S\). Varying the ratios then separates the ordinary symmetric polynomials within each exponent block. Let \(m=m_n\), and let \(B_n\) be the maximum bit length of the denominators of the reduced rational Gram entries. The product of all \(m^2\) denominators is at most \(2^{m^2B_n}\); the positive rational determinant has denominator dividing that product. Therefore

\[
\det G\ge2^{-m^2B_n},\qquad
\lambda_{\min}(G)\ge2^{-m^2B_n}(2m)^{-(m-1)}.
\]

This uses [1/2,2] diagonal scaling and [tr \(G\le2m\)]. Consequently any reduced-normalized real coefficient vector satisfies
\[
\|c\|_2^2\le 2^{h_n},\qquad
h_n=m^2B_n+(m-1)\lceil\log_2(2m)\rceil.
\]
Here \(h_n\) is polynomial in \(n\). The fixed constant angular normalization only changes an overall constant. Rational rounding needs additional bits for the requested residual tolerance and the graph norms of the columns, whose logarithms also have polynomial bounds. This is a coefficient-size argument, not an assertion that floating-point conditioning is mild: the failed E10 check at 512 bits is direct evidence that practical interval conditioning matters.

The future asymptotic algorithm must replace the experiment's fixed tolerances by a schedule such as \(\tau_{n,p}=2^{-h_n-n-p-2}\) and additive solve tolerance \(\delta_{n,p}=2^{-n-p-2}\), with any needed fixed normalization constants accounted for. \(\log2\) and \(\pi\) have the explicit rational series bounds already used. The crude Gram bound, rational symmetric elimination, and matrix-entry height bounds give a concrete polynomial-bit route. A polished proof with all operation-count exponents and constants remains **OPEN**. The finite experiment's \(10^{-16}\) additive tolerance is not itself an arbitrary-precision algorithm.

**OPEN, physical approximation.** Expanding the largest exponent does not automatically approximate a logarithm with arbitrarily high accuracy. The polynomial multiplicities (n-2j), as well as the expanding scales, are essential. A plausible route is high-order Taylor or moment approximation of a valid Laplace representation on dyadic scale intervals, with degree tapering toward the smallest spatial scales. What is missing is a representation or a *direct* weighted graph approximation argument for the actual physical eigenfunction, including simultaneous collision and triple-collision behavior and the exterior tail. A formal Fock solution or one damped logarithmic building block does not discharge this obligation.

C has a real physical advantage: writing \(v=T/S,w=U/S\),
\[
\log(r^2+s^2)=2\log S+\log((1+v^2)/2),\quad
x_1\cdot x_2=S^2[(1+v^2)/4-w^2/2].
\]
Its logarithmic sector captures the radial part of the verified leading Fock term, and ordinary ratio polynomials approximate the remaining analytic angular factor. But a fixed log depth does not supply a theorem for the complete physical eigenfunction. Nor does successful finite arithmetic supply an all-order Gram lower bound: the C Gram entries themselves involve \(\gamma,\log2,\pi^2\), so the rational determinant argument used for E cannot simply be repeated. Analytic norm inequalities might solve this problem; a number-theoretic lower bound is not the only possibility. These are named open obligations, not a claim that C is doomed.

D remains the analytically safer alternative because local weighted derivative estimates feed local geometric approximation directly. An independent review agrees that E is a defensible provisional target for the complete algorithm, while emphasizing that its analytic RATE lemma is not presently more established or demonstrably more plausible than the full hp route. The exact missing LPWA estimate remains that of Section 4 of the prior report, for the *degenerate perimetric operator* and the physical graph norm. Three early cubic tensor stages and six stages of a different shell family do not settle that question. Its local-to-global graph gluing, exterior/tail control, and higher \(O(n^9)\) dimension burden all remain relevant. This study has supplied actual D data and a rational integral route; it has not made D an analytic loser.

### Explicit record of avoided shortcuts

* A fixed pair of exponents was not called adaptive; E adds \(\lfloor n/2\rfloor+1\) prescribed scales.
* The quadratic log used \(x_1\cdot x_2\), and an unsupported physical log-square coefficient was not assumed.
* Every formally negative-power Schwartz term was checked in \(H^2\); the source's \(k=2\) convention was retained.
* The shell hp pilot was not relabeled as the full tensor hp dictionary. Its smaller dimension is reported separately.
* Actual continuum \(H\phi\) moments were used, not \(A G^{-1}A\).
* Finite-pencil residuals were not treated as additive optimization certificates. Survivors received interval LDL checks.
* The 512-bit E10 inconclusive result was retained and resolved by increasing precision, not by changing the trial or tolerances.
* Certificate widths were not substituted for ground residuals; both the variance and the exact self-enclosed ground residual squared are recorded.
* Favorable stretched-exponential fits were not promoted to RATE. Even the refuted control has a favorable finite-window stretched fit.
* No all-order physical eigenfunction representation was inferred from the verified leading Fock factor.
* The second machine checks the same mathematics with another runtime; it is evidence against execution mistakes, not a second proof of shared source formulas.

## Single recommended target and next-session handoff

**RECOMMENDED DICTIONARY:** E, with
\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\mathrm{sym}},
\qquad n\ge0.
\]
For the executed experiment \(Z=2\). The exponent rule, polynomial multiplicities, and dyadic norm scaling are part of the definition.

**EMPIRICAL RATE CONSISTENT WITH:** approximately \(e^{-0.92n}\) decay of the Rayleigh residual over E orders 2–10; the fitted stretched exponent stays at the scan boundary \(\alpha=1\), and the last-two predictions are within about 13%. Against dimension the preferred finite-range exponent is around 0.3. Neither value is an asymptotic claim. The native conjecture allows any fixed \(0<\alpha\le1\), not just the empirically preferred 1.

**NATIVE RATE CONJECTURE TO ATTEMPT:** **OPEN.** For each fixed integer \(Z\ge2\), there exist \(C_Z,c_Z>0\) and (\alpha_Z\in(0,1]) such that, for all \(n\ge0\),
\[
\inf_{\phi\in V_n^{(Z)},\ \|\phi\|_2=1}
\|(H_Z-E_Z)\phi\|_2\le C_Ze^{-c_Zn^{\alpha_Z}}.
\]
For a finite charge class, minima/maxima of the finitely many constants give a common positive exponent and constants. No uniform claim for unbounded \(Z\) is made.

**WHY THIS FAMILY:** it combines verified finite residual decay with deterministic small parameter descriptions, the unchanged exact moment field, and a rational-Gram coefficient bound. Thus a successful physical approximation lemma has an unusually direct route to the remaining effective algorithm obligations.

**WHY EACH OTHER FAMILY LOST:** A is **REFUTED** as a fast RATE target by Theorem C. B's tested improvement tapers and its high-order pilot is substantially weaker; depth one remains analytically **OPEN**. C wins important finite comparisons, but still needs both a direct physical graph approximation theorem and an all-order coefficient/Gram bound; fixed log depth has no verified completeness/rate theorem here. D has the strongest geometric regularity motivation, but its actual tensor pilot gives too little asymptotic evidence and its weighted graph interpolation/global bridge remains substantial. These are proof-priority decisions; B–D are not refuted.

**FIRST ANALYTIC OBSTACLE:** establish quantitative approximation of the *actual* ground state's triple-collision and angular collision structure by this precise deterministic dyadic exponential-polynomial allocation, rather than by a formal local solution or a freely selected exponential set.

**SECOND ANALYTIC OBSTACLE:** combine that local approximation with all two-body collision regions and the exterior tail in the six-dimensional Coulomb operator graph norm, with constants independent of \(n\) and without introducing basis elements outside \(V_n^{(Z)}\).

**EFFECTIVE-DICTIONARY / BIT-COST OBSTACLE:** turn the polynomial height and rational determinant estimates above into an explicit precision/rounding/regularization schedule and operation count. The hardest empirical precision event was E10's 512-bit interval-LDL failure; 1024 bits succeeded. No exponential-in-\(n\) *bit length* is forced by the exponentially large exponents, but all constants must be counted in the future theorem.

**WHAT RESULT WOULD FALSIFY THIS CHOICE:** a lower bound for the best ground residual in this exact expanding dictionary that excludes every \(e^{-c n^\alpha}\), \(\alpha>0\), for example a polynomial lower bound on an infinite subsequence. Reproducible long-range decay collapse would weaken the decision empirically but would not alone prove such a lower bound. A proved C graph RATE together with polynomial coefficient control, or a completed D weighted graph bridge, would also remove E's present proof-priority advantage.

**NEXT PROOF SESSION PROMPT:**

> Prove or refute one statement: deterministic dyadic exponential-polynomial graph RATE for the physical two-electron atomic ground state. Fix an integer \(Z\ge2\). Let \(H_Z=-\tfrac12(\Delta_1+\Delta_2)-Z/|x_1|-Z/|x_2|+1/|x_1-x_2|\) be the self-adjoint Coulomb operator on antisymmetric spin-space wavefunctions, with domain \(H^2\cap\mathcal H_-\), and \(E_Z=\inf\operatorname{spec}H_Z\). Write \(r=|x_1|,s=|x_2|,u=|x_1-x_2|\). Let \(\mathcal P_d^{\mathrm{sym}}\) be all symmetric nonnegative-power polynomials in (r,s,u) of total degree at most \(d\), and define \(V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\mathrm{sym}}\), tensored with the spin singlet. Establish, or give a precise obstruction to, constants \(C_Z,c_Z>0\), \(0<\alpha_Z\le1\), independent of \(n\), for which the normalized best residual is at most \(C_Ze^{-c_Zn^{\alpha_Z}}\) for every \(n\). The dyadic exponents and degree allocation are fixed; changing them is a different theorem. Work with the actual eigenfunction, not an assumed physical realization of a formal Fock expansion. A proof must address triple and pair collisions and the exterior tail in the physical graph norm. A Laplace representation plus high-order approximation on dyadic scale intervals is a possible route, not an available hypothesis. A single logarithmic building block is insufficient. Use the existing finite-domain/moment facts, \(m_n=O(n^4)\), and rational dyadic scaling. The effective coefficient bound is \(\|c\|_2^2\le2^{h_n}\) for reduced-normalized vectors, with \(h_n=m_n^2B_n+(m_n-1)\lceil\log_2(2m_n)\rceil\) and polynomial Gram-denominator height \(B_n\); state how any RATE witness respects that bound, without mistaking it for the approximation proof. Do not assume an unknown eigenvalue as an algorithmic input, substitute an \(H^1\) rate, impose a Coulomb cutoff, or claim Theorem T. If the global statement remains unresolved, isolate the smallest precise physical approximation sublemma left open, rather than replacing the objective with a new computation.

