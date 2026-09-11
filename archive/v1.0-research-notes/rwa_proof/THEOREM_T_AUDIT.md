> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Independent audit of the effective Theorem T composition

**Verdict: PASS — PROVEN (paper), with the global graph-rate premise (GR) supplied by its separate continuum proof and audit.** This audit checks the arithmetic, conditioning, finite optimization, certificate, and cost composition in `THEOREM_T_COMPOSITION.md`. It does not replace the independent analytic audit of (GR), and it does not claim Lean verification or practical tractability.

The audited version includes the two corrections requested during review: it distinguishes rational parameters and matrices `G,A` from the generally transcendental entries of `Q,D,T`; and it initializes reciprocal-quotient bisection at the rational endpoints `1/(2 B₀), 2`, explicitly obtaining a negative witness at the first endpoint. Both corrected arguments pass.

No integral table or numerical experiment was rerun. I inspected the exact all-order branches in `helium/hylleraas.py`, the fixed-shift and dictionary hypotheses used in the existing reports, and every bound and algorithmic step in the composition note.

## 1. Exact data and coefficient heights

**PASS.** The Hamiltonian action has at most 24 uncollected contributions per input monomial and at most 48 per symmetric generator. Consequently a `Q` entry has at most 2304 primitive moments. The apparent repeated lowering of a distance power does not produce an individual exponent below −1 in a nonzero action term: the derivative coefficient vanishes at the potentially offending original exponent. After multiplication by the integration measure, the primitive indices for `G` and `A` are nonnegative. Their entries are therefore rational. Products of two actions can leave a primitive exponent −1, explaining the larger exact linear span needed for `Q`.

The stated primitive-index and exponent-height bounds are conservative. With `D=16N`, counting at most `D²` angular summands, at most three denominator factors per summand, and the explicit radial factorial and exponent denominator gives the claimed cubic height bound. Even product-of-denominators summation, the two generator factorials, dyadic column scaling, and 2304-term entry sums fit within

\[
H_Z(n)=2^{40}(z+1)^2N^3.
\]

The dyadic normalization is exact: a positive rational squared norm can be multiplied by an integer power of four into `[1/2,2]`; the required exponent is bounded by its rational height. The number of generators is at most `N⁴`. Distinct radial exponential-polynomial independence, followed by polynomial independence on the open angular domain, makes the reduced Gram matrix positive definite.

For this rational Gram matrix, the product of its entry denominators clears the determinant. Thus

\[
\det G\ge2^{-m^2B},\qquad
\lambda_{\min}(G)\ge2^{-m^2B}(2m)^{-(m-1)}.
\]

The trace bound uses exactly the prescribed diagonal normalization. Since `m≤N⁴` and `B≤H_Z(n)`, the coefficient-height exponent is `q=11`. The enlarged choice `hₙ=2⁴⁶(z+1)²N¹¹` dominates the displayed terms.

There is no normalization mismatch in applying this bound to the physical witness. If `c_phys` denotes coefficients of a physically normalized function, then `c_physᵀGc_phys=1/(8π²)`. The existential vector `c_red=√(8π²)c_phys` has reduced norm one and obeys the Gram bound. All unregularized physical quotients are unchanged; the regularizer is bounded using `c_red`. This scalar is used only in the proof and is never computed in the rational certificate. Real witnesses suffice: for a complex normalized residual witness, one of its nonzero real or imaginary parts has no greater residual quotient, because the relevant real quadratic forms add.

## 2. Effective dictionary and interval cost

**PASS.** The angular recurrences, including elementary factorial/binomial generation, use at most cubic-in-`N` rational-operation counts per primitive. Charging a rational operation the cube of its cubic height gives exact entry construction in `O_Z(N¹²)` and dictionary generation including the diagonal scaling in `O_Z(N¹⁶)`. Thus `a=16` and `b=4` are safe.

The stated logarithm remainder follows by bounding `1/(2j+1)` by its first omitted value and summing the ratio-`1/9` tail. Machin's identity with alternating arctangent remainders gives rational directed bounds for π and its square. With recursive integer powers, a dyadic accumulation mesh, and logarithmically many guard bits, `O(R)` terms of `O(R+log R)` bits cost `O(R⁴)` even under the deliberately loose cubic rational-operation model. The evaluation precision `R=s+2H_Z(n)+20` absorbs amplification by the exact field coefficients and the fixed number of final operations. Hence the per-entry bound `O_Z((N+s)¹²)`, and therefore `r=12`, hold. No exact-sign decision for a transcendental number is used.

## 3. Rational finite solve and retained witness

**PASS after the explicit initialization correction.** The physical lower bound and fixed shift imply `D≥G` and `T=D+τI≥τI`. The anchor already in the dictionary supplies `1/B₀≤λ≤1`, where `λ=max G/T` and `B₀=(1+2Z)²+2`.

For the prescribed entry accuracy, let

\[
e=mK_\sigma\zeta
 =\frac{\tau\delta}{2^{20}B_0^2m},
\qquad a=\frac{4e}{\tau}
 =\frac{\delta}{2^{18}B_0^2m}.
\]

Both operator errors are at most `e≤τ/2`. Subtracting reciprocal quotients on Euclidean unit vectors gives the uniform error bound `a`. This bound does not assume that the approximate numerator is positive definite.

The approximate maximum exceeds `1/(2B₀)` and lies below `2`. The initial exact PSD test at the lower threshold therefore produces a rational negative witness. Retaining such a witness whenever the lower threshold increases avoids the possibility of terminating without a vector. With final bracket width

\[
w=\frac{\delta}{2^{12}B_0^2},
\]

the exact reciprocal quotient of the retained witness is at least `λ−w−2a>1/(2B₀)`. Inversion yields an objective error at most `4B₀²(w+2a)<δ`, proving the claimed finite-solve tolerance with room to spare.

The PSD procedure handles singular matrices constructively. For its zero-diagonal block, the proposed vector has quadratic form `b²(d−2|d|−2)<0`. Positive-pivot Schur complements and exact lifting cover the other cases. Clearing the dyadic denominator first and expressing Schur entries and lifted witnesses through minors bounds their common integer-coordinate height by `O(m(B+log m))`. The use of a common denominator is material: multiplying independent coordinate denominators during a naive implementation would give a needlessly larger bound. The specified implementation avoids that loss.

## 4. Final certificate and termination

**PASS.** After rescaling the witness to maximum coordinate magnitude one, its Euclidean squared norm is at least one. The reciprocal-quotient lower bound and `T≥τI` give `cᵀGc≥τ/(2B₀)`. The exact rational mean and the signed `Q` entry intervals consequently bound the second-moment interval width by

\[
\frac{4B_0m^2\zeta}{\tau}
 =\frac{\delta}{2^{18}B_0K_\sigma}
 <\frac{\delta}{2^{17}}.
\]

Subtracting the exact mean square introduces no further interval error. The upper variance endpoint is valid; intersecting its lower endpoint with zero is harmless. The rational mean filter ensures `β−m≥g>0`, so Temple's theorem proves each accepted enclosure. This correctness statement does not depend on (GR).

Under (GR), the spectral gap converts the residual witness into a shifted-objective witness, and the coefficient regularizer plus finite-solve error add `2δ`. Thus the displayed excess bound `εₙ` gives `m−E_Z≤εₙ/2` and `v≤εₙ`. The previously proved strict anchor margin `μ_Z=U−E_Z>0` ensures that the mean filter eventually passes.

The two sufficient index inequalities (17) imply `A_Z exp(−2c_R n^(1/16))≤t/2` and `δ≤t/4096`. Therefore `εₙ<t`, the variance enclosure error is smaller still, and the two endpoint roundings add at most `2δ`. The certified width is below `2^(−p)`. No unknown convergence constant or exact energy is required by the adaptive loop.

For an explicit elementary stopping constant, set

\[
Q_Z=\max\{0,\log_2(\mu_Z^{-1}),\log_2(g^{-1})\},
\quad B_Z=\max\{0,\log(2A_Z)\}+(Q_Z+5)\log2.
\]

For integer `p≥0`, one may take, for example,

\[
C'_Z=Q_Z+10+\left(\frac{B_Z}{2c_R}\right)^{16}.
\]

Indeed, `log(2A_Z/t)≤B_Z(p+1)` whenever the left side is positive, and `log₂(4/t)≤p+6+Q_Z`. Taking the ceiling of the maximum sufficient index, also imposing `n≥1`, is bounded by `C'_Z(p+1)¹⁶`. This supplies a concrete choice for the traceable constant described in the composition note. It is a mathematical convergence constant, not an input to the algorithm.

## 5. Final bit exponent and scope

**PASS.** The required entry precision is `O_Z(N¹¹)`. There are `O(N⁸)` entries, so the deliberately enlarged entry-cost estimate gives stage exponent `8+12·11=140`. Fraction-free PSD tests, witness construction, and exact final contractions have the smaller bound `O_Z(N⁵³)` using common denominators. In particular the exact common denominator for all field entries has `O_Z(N¹¹)` bits, the retained witness has `O_Z(N¹⁵)` coordinate height, and the final contractions can maintain those common denominators instead of accumulating artificial products.

Summing stage cost through `O_Z((p+1)¹⁶)` stages gives

\[
\text{total bit cost}\le C_Z(p+1)^{2256},
\qquad2256=16(140+1).
\]

The integer exponents `a=16,b=4,q=11,r=12` and the final exponent 2256 are therefore justified upper bounds. The multiplier depends on the fixed charge, the arithmetic construction constants, the separate graph-rate constants, and the strict anchor margin. Taking a maximum over finitely many charges is legitimate. This does not provide a uniform result for arbitrary nuclei or electron number, a useful practical exponent, or a Lean formalization of the analytic or algorithmic proof. The physical discharge of (GR) remains the subject of `GLOBAL_DYADIC_ATTEMPT.md` and `GLOBAL_DYADIC_AUDIT.md`, not a consequence of this arithmetic audit.

No numerical output is promoted to a proof, and no additional open lemma was found in the effective composition as corrected.
