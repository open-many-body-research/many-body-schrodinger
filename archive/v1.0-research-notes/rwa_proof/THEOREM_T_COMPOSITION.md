> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Effective composition with the dyadic graph rate

**PROVEN (paper), conditional only in the final energy-cost conclusion on the global graph RATE stated below.** The effective-dictionary and finite-solve results in this note do not assume RATE. This is an operation-count proof for a specified rational algorithm, not a claim that the old fixed-tolerance screening program implements that algorithm. No new numerical experiment or Lean theorem is asserted.

**Completed physical application — PROVEN (paper).** The sole analytic premise (GR) is now proved for the actual fixed-charge atom in [GLOBAL_DYADIC_ATTEMPT.md](GLOBAL_DYADIC_ATTEMPT.md), with its physical inputs discharged and its [independent audit](GLOBAL_DYADIC_AUDIT.md) complete. Therefore the algorithm and cost bound below prove Theorem T for every fixed integer \(Z\ge2\). The conditional formulation is retained to make the dependency separation explicit. The separate effective/algorithm audit is [THEOREM_T_AUDIT.md](THEOREM_T_AUDIT.md).

Fix an integer \(Z\ge2\). Put \(N=n+2\), \(z=1+\lceil\log_2(Z+1)\rceil\), and retain exactly
\[
 V_n=\sum_{j=0}^{\lfloor n/2\rfloor}e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\rm sym}.
\]
The generator at exponent \(\alpha=Z2^j\) is the symmetric monomial of degree \(d\le n-2j\), divided by \(d!\), and multiplied by a rational power of two making its reduced squared norm lie in \([1/2,2]\). “Reduced” omits the common angular factor \(8\pi^2\) in every scalar product. Quotients and the differential operator are unaffected. No extra core, cutoff, logarithmic column, or continuously selected exponent is appended.

The bit model is the usual deterministic arithmetic bit-cost model: integers are binary strings; addition, multiplication, exact division and rational comparisons are charged their schoolbook bit costs. Array/index and loop overhead can be implemented within the conservative counts below. In particular a rational arithmetic operation on height-\(b\) reduced fractions may be charged \(O(b^3)\); this allows even a deliberately loose bound for gcd reduction. Fraction-free integer elimination uses \(O(b^2)\) multiplication/division bounds.

## 1. Exact moments and explicit height bound

The finite recurrences are those in `helium/hylleraas.py`, with the derivation already recorded in `helium/THEORY.md` and the mixed-exponent extension in `RATE_DICTIONARY_DECISION.md`. The following audit concerns their all-order size and cost, rather than new integral identities.

One symmetric generator has at most two monomials. The displayed Hamiltonian action in `h_action` contributes at most 24 Laurent terms per input monomial, hence at most 48 terms before collection. A matrix entry of \(Q_{ij}=\langle H\phi_i,H\phi_j\rangle\) therefore involves at most \(48^2=2304\) primitive moments; \(G\) and \(A\) involve fewer. All primitive moment indices obey
\[
 a,b,c\ge-1,\quad a+b+c>-3,
 \quad \max(a,b,c)\le2n+5,\quad a+b+c\le2n+3.
\]
The exponent sum \(\kappa=Z(2^i+2^j)\) has at most \(z+N+2\) bits. Each primitive moment has the exact form
\[
 \frac{2^{-a-b-1}(a+b+c+2)!}{\kappa^{a+b+c+3}}
 (q_0+q_1\log2+q_2\pi^2),\qquad q_i\in\mathbb Q.
\tag{1}
\]
Let \(D=16N\). Every integer denominator factor in the angular loops is at most \(D\). In the ordinary-polynomial branch, a denominator has at most two factors. In the inverse-\(r\) branch, the additional division by \(c+1\) makes at most three factors. The inverse-\(u\) branch has squared odd denominators. Thus \((D!)^3\) is one possible common angular denominator. This observation also covers intermediate partial-fraction sums; their individual summands are integrable grouped quantities from the endpoint-safe recurrence.

For a bound that does not require an optimized common-denominator implementation, there are at most \(D^2\) angular rational summands, each with denominator at most \(D^3\). Keeping the product of their denominators gives at most
\[
 3D^2\log_2D\le2304N^3
\]
denominator bits, since \(\log_2(16N)\le3N\) for \(N\ge2\). Binomial coefficients contribute at most (2D) additional bits per summand, and summation contributes at most \(2\log_2D\) more. The radial factor contributes at most \(D(z+N+2)+D\log_2D+D\) bits. These estimates bound each primitive coefficient and every intermediate by
\[
 H_{\rm primitive}=2^{13}(z+1)N^3.
\]
The deliberately enlarged bounds below allow all generator factorials, coefficient products, and additions as well.

An unscaled diagonal \(G_{ii}>0\) is a sum of at most four primitive terms with two generator factorial factors. Its numerator and denominator heights are bounded by \(2^{17}(z+1)N^3\). A positive rational of height \(b\) lies between \(2^{-b}\) and \(2^b\); consequently the dyadic column-scaling exponent has absolute value at most that bound. Scaling is found by integer bit lengths and at most a fixed number of exact comparisons. Hamiltonian-action coefficients introduce only degree factors, \(Z\), \(\alpha\), \(\alpha^2\), and halves. Finally there are at most 2304 products to add per entry. Even bounding a sum by the product of all its denominators gives the following single explicit bound on every numerator and denominator of the three field coefficients of every scaled \(G,A,Q\) entry, and on intermediates in this construction:
\[
 \boxed{H_Z(n)=2^{40}(z+1)^2N^3.}
\tag{2}
\]
For example, allowing \(2^{24}(z+1)N^3\) for a scaled action coefficient, a product with a primitive moment has height below \(2^{26}(z+1)N^3\); adding at most 2304 such terms costs fewer than another 12 powers of two in this estimate. Thus (2) has spare room. The large numerical multiplier is a proof bound, not a recommended numerical precision.

Both \(G\) and \(A\) are rational, not just elements of the three-dimensional moment field. In \(G\), the measure \(rsu\) makes all primitive powers nonnegative. In \(A\), one undifferentiated polynomial is multiplied by a single Hamiltonian action. Every nonzero action term has each distance power at least \(-1\): the apparently twice-lowered \(u\) powers in a mixed derivative carry a factor \(k\), so \(k\ge1\); radial second derivatives carry the factors \(i(i-1)\) or \(j(j-1)\). The measure again makes every primitive power nonnegative. This is the ordinary-polynomial angular branch, with rational radial factors, so neither \(\log2\) nor \(\pi^2\) occurs. A product of two actions in \(Q\) can have primitive powers \(-1\), which is why its field is larger. Dyadic scaling preserves these facts.

Positive definiteness follows from independence of exponential polynomials at distinct exponents after fixing interior angular ratios and varying \(r+s\), followed by polynomial independence as those ratios vary. The generator count satisfies
\[
 m_n\le N^4.
\tag{3}
\]

The nested angular loops, including elementary generation of binomial coefficients and factorials, need \(O(N^3)\) rational operations per primitive moment. Charging each operation the cube of (2) proves exact-entry construction in \(O_Z(N^{12})\) bit operations. The constant 2304 does not affect the exponent. Dictionary generation including exact diagonal scaling therefore costs \(O_Z(N^{16})\).

## 2. Interval evaluation has polynomial precision cost

To evaluate an entry to absolute error \(2^{-s}\), first construct its three rational coefficients exactly. Their integer-part sizes are already bounded by (2). Evaluate the two universal constants to \(R=s+2H_Z(n)+20\) bits, rounding every retained arithmetic result outward on a dyadic mesh. Use
\[
 \log2=2\sum_{j=0}^{K-1}\frac1{(2j+1)3^{2j+1}}+R_K,
 \quad 0<R_K\le\frac9{4(2K+1)3^{2K+1}},
\]
and Machin's identity \(\pi=16\arctan(1/5)-4\arctan(1/239)\), with alternating-series next-term remainders. Taking \(K=O(R)\) terms suffices. An additional \(O(\log(R+2))\) guard bits covers the accumulated outward rounding. Powers are maintained recursively, so every term and dyadic rounding operation has \(O(R+\log(R+2))\) bits. Even charging cubic rational-operation cost gives \(O(R^4)\) bit operations. Since \(R=O_Z((N+s)^3)\),
\[
 \boxed{\text{one entry to }2^{-s}\text{ costs }O_Z((N+s)^{12}).}
\tag{4}
\]
Multiplication by field coefficients uses their signs and interval endpoints. There is no floating point or exact-sign oracle for a transcendental expression. The rational interval remainder and rounding bounds are part of the algorithm.

## 3. Coefficient control and schedules

Let \(B_n\) be the maximum denominator height of the reduced rational Gram entries. The existing determinant argument, recalled here, gives
\[
 \det G\ge2^{-m_n^2B_n},\qquad
 \lambda_{\min}(G)\ge2^{-m_n^2B_n}(2m_n)^{-(m_n-1)}.
\]
Thus every real vector with \(c^TGc=1\), including an existential best-approximation witness, obeys
\[
 \|c\|^2\le2^{h_n},\quad
 h_n\ge m_n^2B_n+(m_n-1)\lceil\log_2(2m_n)\rceil.
\tag{5}
\]
Enlarge \(h_n\) to dominate matrix-norm logarithms and parameter heights. One completely explicit choice is
\[
 \boxed{h_n=2^{46}(z+1)^2(n+2)^{11}.}
\tag{6}
\]
A less wasteful algorithm can compute the right side of (5) from the exact entries and take its maximum with their actual height bounds; (6) proves the all-order estimate in either case. The exponent is \(q=11\). Physical normalization only multiplies the reduced trial by a fixed scalar; all quotients, residuals, and (5) in reduced normalization retain their meaning.

Set, for \(n=1,2,\ldots\),
\[
 L=-Z^2,\quad U=-Z^2+5Z/8,\quad \beta=-5Z^2/8,
 \quad g=Z(3Z-5)/8,
\]
\[
 \sigma=L-1,\qquad
 \tau_n=2^{-h_n-n-10},\qquad \delta_n=2^{-n-10}.
\tag{7}
\]
Use the corrected fixed-shift objective
\[
 J_{\tau_n}(c)=\frac{c^T(D+\tau_n I)c}{c^TGc},\qquad
 D=Q-2\sigma A+\sigma^2G.
\tag{8}
\]
The parameters, \(G\), and \(A\) are known rational data. The matrices \(Q,D,T\) generally have coefficients in the known linear span \(\mathbb Q+\mathbb Q\log2+\mathbb Q\pi^2\); their certified dyadic approximations, rather than an exact transcendental sign oracle, are used in the finite PSD tests below. The algorithm never receives \(E_Z\), RATE constants, an optimal coefficient vector, or the physical analytic-continuation constants.

## 4. A fully rational finite solve and final certificate

Because \(H_Z-\sigma\ge I\), \(D\ge G\). Put \(T=D+\tau_n I\). The \(j=0,d=0\) anchor is already in \(V_n\), so it need not be appended. Its reduced norm lies in \([1/2,2]\). Hardy's bound gives its physical shifted quotient at most \((1+2Z)^2\), while its regularizer contributes at most \(2\tau_n\). Therefore with
\[
 B_0=(1+2Z)^2+2,
 \quad \lambda_n=\max_{c\ne0}\frac{c^TGc}{c^TTc},
\]
we have \(1/B_0\le\lambda_n\le1\).

Let \(K_\sigma=2+2|\sigma|+\sigma^2\), and compute dyadic approximations to every \(G,A,Q\) entry with error at most
\[
 \zeta_n=\frac{\tau_n\delta_n}{2^{20}B_0^2m_n^2K_\sigma}.
\tag{9}
\]
Round all approximations to a common dyadic denominator. This takes
\[
 s_n=O_Z(h_n+n+\log(m_n+2))=O_Z(N^{11})
\tag{10}
\]
fractional bits, with the integer heights included. The approximate \(\widetilde T\) stays positive definite. If two numerator/denominator operators have errors at most \(e\le\tau_n/2\), their reciprocal quotients change by at most \(4e/\tau_n\): subtract the two fractions after imposing \(\|c\|=1\), use the exact denominator \(\ge\tau_n\), the approximate denominator \(\ge\tau_n/2\), and \(0\le c^TGc\le c^TTc\). Bound (9) is much stronger than needed for that estimate.

Initialize bisection with the exact rational endpoints \(1/(2B_0)\) and \(2\). First test the lower endpoint and retain its rational negative witness; the perturbation allowance guarantees that this endpoint is strictly below the approximate maximum, so that witness exists. The upper endpoint is above that maximum. Bisect the largest quotient of \(\widetilde G/\widetilde T\) using exact PSD tests of \(t\widetilde T-\widetilde G\), updating the retained witness whenever the lower threshold increases. Stop when the interval width is at most \(\delta_n/(2^{12}B_0^2)\). Its lower threshold is then within that tolerance of the approximate maximum. The exact quotient of the retained vector is at least \(1/B_0\) minus the two perturbation allowances and this tolerance, hence exceeds \(1/(2B_0)\). Inversion, together with those same bounds, proves that the returned rational vector satisfies
\[
 J_{\tau_n}(c_n)\le\inf J_{\tau_n}+\delta_n.
\tag{11}
\]
There is no precision loop for singular comparisons: the matrix being tested is an already fixed rational matrix.

For completeness, exact symmetric elimination makes the PSD decision constructive. A negative diagonal gives its coordinate vector. A zero diagonal with a nonzero off-diagonal entry gives a negative rational two-coordinate vector: for the corresponding block \(\left(\begin{smallmatrix}0&b\\b&d\end{smallmatrix}\right)\), take \((-(|d|+1)\operatorname{sign}b,|b|)\); its quadratic form is strictly negative. A zero row and column can be deleted. Otherwise a positive pivot produces a Schur complement; lift a negative vector through the triangular elimination. An entirely positive sequence proves PSD. Clearing the common dyadic denominator first, fraction-free elimination and minor formulas produce a witness whose integer coordinates have \(O(m_n(B+\log m_n))\) bits when the input entries have \(B\) bits. A common denominator can be retained for all witness coordinates. This prevents an artificial product of independently introduced coordinate denominators during final contraction.

Rescale the witness so \(\|c_n\|_\infty=1\). Its exact reciprocal quotient is at least \(1/(2B_0)\), so
\[
 c_n^TGc_n\ge\tau_n/(2B_0).
\tag{12}
\]
Compute the mean \(m=c_n^TAc_n/(c_n^TGc_n)\) **exactly rationally**, and the second moment with the signed entry intervals from (9). Since \(\|c_n\|^2\le m_n\), its certified second-moment interval has width at most
\[
 \frac{2m_n^2\zeta_n}{\tau_n/(2B_0)}<\delta_n/2^{17}.
\]
Intersect the variance lower endpoint with zero. If \(m>U\), skip the stage. Otherwise \(\beta-m\ge g>0\); with a certified variance upper bound \(v_+\), form
\[
 [\ell,u]=\left[m-\frac{v_+}{\beta-m},\ m\right]
\tag{13}
\]
and round both endpoints outward to the dyadic mesh \(2^{-n-10}\mathbb Z\). Stop exactly when \(u-\ell\le2^{-p}\). All acceptance decisions are rational decisions. The continuum separator and Temple theorem from `TWO_ELECTRON_THEOREM.md` prove every emitted enclosure correct, whether or not RATE is known.

## 5. Cost and conditional Theorem T

The concrete effective exponents established above are
\[
 \boxed{a=16,\quad b=4,\quad q=11,\quad r=12.}
\tag{14}
\]
There are \(O(N^8)\) entries, each evaluated at \(s_n=O_Z(N^{11})\). Equation (4) gives the deliberately coarse entry-assembly exponent \(8+12\cdot11=140\). The exact symbolic entry construction and dictionary generation are smaller.

For the rational PSD solve, fraction-free intermediates have \(O(m_n(B+\log m_n))\) bits. There are \(O(m_n^3)\) arithmetic operations per test, so schoolbook multiplication/division gives \(O(m_n^5(B+\log m_n)^2)\). The number of bisections is at most \(O_Z(s_n)\); in fact the displayed stopping threshold permits a smaller bound. Thus the earlier safe exponent \(5b+3q=53\) applies. A common denominator for all exact field entries has at most \(O(m_n^2H_Z(n))=O_Z(N^{11})\) bits. Combined with the common-denominator witness, whose coordinate height is \(O_Z(N^{15})\), exact final contractions need at most \(O_Z(N^{53})\) using the conservative cubic rational-operation cost. Endpoint rounding and hashing/output, if requested, are smaller. Hence
\[
 \boxed{\text{stage }n\text{ costs }O_Z((n+2)^{140})\text{ bit operations}.}
\tag{15}
\]
These exponents are upper bounds selected for transparent proof, not estimates of practical cost.

Now assume the **global RATE premise**, and nothing stronger about computing its witnesses:
\[
 \exists C_R,c_R>0\quad\forall n\ge1\quad
 \inf_{\phi\in V_n,\ \|\phi\|=1}
 \|(H_Z-E_Z)\phi\|\le C_Re^{-c_R n^{1/16}}.
\tag{GR}
\]
With \(d=E_Z-\sigma\), \(1\le d\le1+5Z/8\), and
\[
 K_Z=1+\frac{2(1+5Z/8)}g,
\]
the existing scalar spectral estimate and (5), (7), (11) give the physical shifted excess
\[
 \|(H_Z-\sigma)\phi_n\|^2-d^2
 \le\epsilon_n:=K_ZC_R^2e^{-2c_Rn^{1/16}}+2\delta_n.
\tag{16}
\]
Here \(\phi_n\) is the physical normalization of the rational output; normalization is an analysis step and no square root enters the certificate. Consequently
\[
 m-E_Z\le\epsilon_n/2,\qquad v\le\epsilon_n.
\]
The strict inequality \(\mu_Z:=U-E_Z>0\) was proved in the old report. Once \(\epsilon_n\le\mu_Z\), the mean filter \(m\le U\) succeeds. The sufficient index for this filter is a fixed charge-dependent constant. It is not an extra code input or an additional unresolved lemma.

For an explicit trace of the termination constant, write \(A_Z=K_ZC_R^2\) and define
\[
 t_{Z,p}=\min\{\mu_Z,\ g\,2^{-p-4},\ 2^{-p-4}\}.
\]
It suffices to take any integer \(n\ge1\) such that
\[
 n\ge\left[\frac{\max(0,\log(2A_Z/t_{Z,p}))}{2c_R}\right]^{16},
 \qquad n\ge\log_2(4/t_{Z,p}).
\tag{17}
\]
Then \(\epsilon_n\le t_{Z,p}\), the interval error from (9) is much smaller than \(\delta_n\), and (13), including both outward roundings, has width \(\le2^{-p}\). The inequalities show \(n\le C'_Z(p+1)^{16}\), with \(C'_Z\) a specified elementary function of \(C_R,c_R,g,\mu_Z\). These are mathematical convergence constants; the adaptive loop never has to know them.

Summing (15) through that stopping index proves
\[
 \boxed{\text{total bit cost}\le C_Z(p+1)^{2256},\qquad2256=16(140+1).}
\tag{18}
\]
The multiplier \(C_Z\) is obtained from the schoolbook-arithmetic and moment bounds in §§1–5, multiplied by a constant times \((C'_Z)^{141}\). Thus its dependencies are traceable; no numerical bound on the analytic RATE constants is claimed here. For the fixed finite class \(2\le Z\le Z_{\max}\), take the maximum of the finitely many constants, with the same exponent 2256.

**Conditional conclusion.** If (GR) is established by the continuum proof, the specified deterministic rational algorithm proves Theorem T for the fixed charge-\(Z\) two-electron atom, with the conservative exponent 2256. The proof does not require a computable analytic continuation oracle, a computable RATE witness, floating eigenvectors, or prior ground-energy digits. Conversely, the effective lemmas and this composition do not establish (GR); that is a separate analytic dependency. No assertion here concerns varying electron number, arbitrary molecular geometry, a practical polynomial bound, or Lean verification of the algorithm.
