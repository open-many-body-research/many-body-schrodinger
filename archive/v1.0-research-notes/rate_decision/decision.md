> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

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

**PROVEN (this session), elementary effective-dictionary checks for E.** The exponents and degree allocation are deterministic, with no continuous optimization of exponent locations. Each generator is dyadically rescaled so that its reduced norm squared is in [1/2,2]. Degrees are (O(n)), exponents and exponent sums have (O(n)) bits, factorials have (O(n\log(n+2))) bits, and every finite polynomial expansion has polynomially many terms. Thus the rational coefficients of (G,A,Q) in the fixed moment field have polynomial bit height. Values such as the high kinetic-energy matrix entries can grow exponentially in (n); their *bit lengths* remain polynomial.

The Gram matrix is rational and positive definite. To see independence, fix an interior pair of angular ratios and vary (S=r+s>0). Distinct exponent polynomial sums are linearly independent as functions of (S). Varying the ratios then separates the ordinary symmetric polynomials within each exponent block. Let (m=m_n), and let (B_n) be the maximum bit length of the denominators of the reduced rational Gram entries. The product of all (m^2) denominators is at most (2^{m^2B_n}); the positive rational determinant has denominator dividing that product. Therefore

\[
\det G\ge2^{-m^2B_n},\qquad
\lambda_{\min}(G)\ge2^{-m^2B_n}(2m)^{-(m-1)}.
\]

This uses [1/2,2] diagonal scaling and [tr (G\le2m)]. Consequently any reduced-normalized real coefficient vector satisfies
\[
\|c\|_2^2\le 2^{h_n},\qquad
h_n=m^2B_n+(m-1)\lceil\log_2(2m)\rceil.
\]
Here (h_n) is polynomial in (n). The fixed constant angular normalization only changes an overall constant. Rational rounding needs additional bits for the requested residual tolerance and the graph norms of the columns, whose logarithms also have polynomial bounds. This is a coefficient-size argument, not an assertion that floating-point conditioning is mild: the failed E10 check at 512 bits is direct evidence that practical interval conditioning matters.

The future asymptotic algorithm must replace the experiment's fixed tolerances by a schedule such as (\tau_{n,p}=2^{-h_n-n-p-2}) and additive solve tolerance (\delta_{n,p}=2^{-n-p-2}), with any needed fixed normalization constants accounted for. (\log2) and (\pi) have the explicit rational series bounds already used. The crude Gram bound, rational symmetric elimination, and matrix-entry height bounds give a concrete polynomial-bit route. A polished proof with all operation-count exponents and constants remains **OPEN**. The finite experiment's (10^{-16}) additive tolerance is not itself an arbitrary-precision algorithm.

**OPEN, physical approximation.** Expanding the largest exponent does not automatically approximate a logarithm with arbitrarily high accuracy. The polynomial multiplicities (n-2j), as well as the expanding scales, are essential. A plausible route is high-order Taylor or moment approximation of a valid Laplace representation on dyadic scale intervals, with degree tapering toward the smallest spatial scales. What is missing is a representation or a *direct* weighted graph approximation argument for the actual physical eigenfunction, including simultaneous collision and triple-collision behavior and the exterior tail. A formal Fock solution or one damped logarithmic building block does not discharge this obligation.

C has a real physical advantage: writing (v=T/S,w=U/S),
\[
\log(r^2+s^2)=2\log S+\log((1+v^2)/2),\quad
x_1\cdot x_2=S^2[(1+v^2)/4-w^2/2].
\]
Its logarithmic sector captures the radial part of the verified leading Fock term, and ordinary ratio polynomials approximate the remaining analytic angular factor. But a fixed log depth does not supply a theorem for the complete physical eigenfunction. Nor does successful finite arithmetic supply an all-order Gram lower bound: the C Gram entries themselves involve (\gamma,\log2,\pi^2), so the rational determinant argument used for E cannot simply be repeated. Analytic norm inequalities might solve this problem; a number-theoretic lower bound is not the only possibility. These are named open obligations, not a claim that C is doomed.

D remains the analytically safer alternative because local weighted derivative estimates feed local geometric approximation directly. An independent review agrees that E is a defensible provisional target for the complete algorithm, while emphasizing that its analytic RATE lemma is not presently more established or demonstrably more plausible than the full hp route. The exact missing LPWA estimate remains that of Section 4 of the prior report, for the *degenerate perimetric operator* and the physical graph norm. Three early cubic tensor stages and six stages of a different shell family do not settle that question. Its local-to-global graph gluing, exterior/tail control, and higher (O(n^9)) dimension burden all remain relevant. This study has supplied actual D data and a rational integral route; it has not made D an analytic loser.

### Explicit record of avoided shortcuts

* A fixed pair of exponents was not called adaptive; E adds (\lfloor n/2\rfloor+1) prescribed scales.
* The quadratic log used (x_1\cdot x_2), and an unsupported physical log-square coefficient was not assumed.
* Every formally negative-power Schwartz term was checked in (H^2); the source's (k=2) convention was retained.
* The shell hp pilot was not relabeled as the full tensor hp dictionary. Its smaller dimension is reported separately.
* Actual continuum (H\phi) moments were used, not (A G^{-1}A).
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
For the executed experiment (Z=2). The exponent rule, polynomial multiplicities, and dyadic norm scaling are part of the definition.

**EMPIRICAL RATE CONSISTENT WITH:** approximately (e^{-0.92n}) decay of the Rayleigh residual over E orders 2–10; the fitted stretched exponent stays at the scan boundary (\alpha=1), and the last-two predictions are within about 13%. Against dimension the preferred finite-range exponent is around 0.3. Neither value is an asymptotic claim. The native conjecture allows any fixed (0<\alpha\le1), not just the empirically preferred 1.

**NATIVE RATE CONJECTURE TO ATTEMPT:** **OPEN.** For each fixed integer (Z\ge2), there exist (C_Z,c_Z>0) and (\alpha_Z\in(0,1]) such that, for all (n\ge0),
\[
\inf_{\phi\in V_n^{(Z)},\ \|\phi\|_2=1}
\|(H_Z-E_Z)\phi\|_2\le C_Ze^{-c_Zn^{\alpha_Z}}.
\]
For a finite charge class, minima/maxima of the finitely many constants give a common positive exponent and constants. No uniform claim for unbounded (Z) is made.

**WHY THIS FAMILY:** it combines verified finite residual decay with deterministic small parameter descriptions, the unchanged exact moment field, and a rational-Gram coefficient bound. Thus a successful physical approximation lemma has an unusually direct route to the remaining effective algorithm obligations.

**WHY EACH OTHER FAMILY LOST:** A is **REFUTED** as a fast RATE target by Theorem C. B's tested improvement tapers and its high-order pilot is substantially weaker; depth one remains analytically **OPEN**. C wins important finite comparisons, but still needs both a direct physical graph approximation theorem and an all-order coefficient/Gram bound; fixed log depth has no verified completeness/rate theorem here. D has the strongest geometric regularity motivation, but its actual tensor pilot gives too little asymptotic evidence and its weighted graph interpolation/global bridge remains substantial. These are proof-priority decisions; B–D are not refuted.

**FIRST ANALYTIC OBSTACLE:** establish quantitative approximation of the *actual* ground state's triple-collision and angular collision structure by this precise deterministic dyadic exponential-polynomial allocation, rather than by a formal local solution or a freely selected exponential set.

**SECOND ANALYTIC OBSTACLE:** combine that local approximation with all two-body collision regions and the exterior tail in the six-dimensional Coulomb operator graph norm, with constants independent of (n) and without introducing basis elements outside (V_n^{(Z)}).

**EFFECTIVE-DICTIONARY / BIT-COST OBSTACLE:** turn the polynomial height and rational determinant estimates above into an explicit precision/rounding/regularization schedule and operation count. The hardest empirical precision event was E10's 512-bit interval-LDL failure; 1024 bits succeeded. No exponential-in-(n) *bit length* is forced by the exponentially large exponents, but all constants must be counted in the future theorem.

**WHAT RESULT WOULD FALSIFY THIS CHOICE:** a lower bound for the best ground residual in this exact expanding dictionary that excludes every (e^{-c n^\alpha}), (\alpha>0), for example a polynomial lower bound on an infinite subsequence. Reproducible long-range decay collapse would weaken the decision empirically but would not alone prove such a lower bound. A proved C graph RATE together with polynomial coefficient control, or a completed D weighted graph bridge, would also remove E's present proof-priority advantage.

**NEXT PROOF SESSION PROMPT:**

> Prove or refute one statement: deterministic dyadic exponential-polynomial graph RATE for the physical two-electron atomic ground state. Fix an integer (Z\ge2). Let (H_Z=-\tfrac12(\Delta_1+\Delta_2)-Z/|x_1|-Z/|x_2|+1/|x_1-x_2|) be the self-adjoint Coulomb operator on antisymmetric spin-space wavefunctions, with domain (H^2\cap\mathcal H_-), and (E_Z=\inf\operatorname{spec}H_Z). Write (r=|x_1|,s=|x_2|,u=|x_1-x_2|). Let (\mathcal P_d^{\mathrm{sym}}) be all symmetric nonnegative-power polynomials in (r,s,u) of total degree at most (d), and define (V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\mathrm{sym}}), tensored with the spin singlet. Establish, or give a precise obstruction to, constants (C_Z,c_Z>0), (0<\alpha_Z\le1), independent of (n), for which the normalized best residual is at most (C_Ze^{-c_Zn^{\alpha_Z}}) for every (n). The dyadic exponents and degree allocation are fixed; changing them is a different theorem. Work with the actual eigenfunction, not an assumed physical realization of a formal Fock expansion. A proof must address triple and pair collisions and the exterior tail in the physical graph norm. A Laplace representation plus high-order approximation on dyadic scale intervals is a possible route, not an available hypothesis. A single logarithmic building block is insufficient. Use the existing finite-domain/moment facts, (m_n=O(n^4)), and rational dyadic scaling. The effective coefficient bound is (\|c\|_2^2\le2^{h_n}) for reduced-normalized vectors, with (h_n=m_n^2B_n+(m_n-1)\lceil\log_2(2m_n)\rceil) and polynomial Gram-denominator height (B_n); state how any RATE witness respects that bound, without mistaking it for the approximation proof. Do not assume an unknown eigenvalue as an algorithmic input, substitute an (H^1) rate, impose a Coulomb cutoff, or claim Theorem T. If the global statement remains unresolved, isolate the smallest precise physical approximation sublemma left open, rather than replacing the objective with a new computation.
