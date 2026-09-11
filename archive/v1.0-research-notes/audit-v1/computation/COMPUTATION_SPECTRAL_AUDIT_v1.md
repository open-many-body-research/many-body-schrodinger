> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Computation and spectral audit, version 1

Date: 2026-09-09. This is new post-freeze work. The frozen originals were read only. This report does not discharge the separately audited global approximation premise and does not certify a Lean implementation of Theorem T.

The finite arithmetic and two-electron spectral arguments inspected here have no identified mathematical counterexample after the checks below. The strongest supported outcome from this part of the audit is an explicit **conditional paper composition**: the stated exact-dictionary global residual rate, together with the stated continuum foundations, implies the proposed fixed-charge polynomial precision bound. The number 2256 is the resulting conservative arithmetic exponent. It is not an observed runtime or a Lean-verified complexity theorem. The existing executable finite experiment uses a different, fixed precision and regularization schedule.

## Provenance and coverage

The authoritative frozen root is `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The differently named `THEOREM_T_FREEZE_2026-09-09/` was not used as a write destination. Exact frozen relative paths, SHA-256 values, and manifest comparisons are recorded in `coverage_and_hashes_v1.json`. All 18 checked hashes matched `FREEZE_MANIFEST.json`.

Full-text coverage in this audit:

- `TWO_ELECTRON_THEOREM.md` (601 lines), including Theorem C, the historical variance-selection counterexample, and the stated formal scope.
- `RATE_DICTIONARY_DECISION.md` (286 lines), including the alternative dictionaries, reported finite data, exact moment class, and original open obligations.
- `helium/THEORY.md` (108 lines), `helium/hylleraas.py` (150 lines).
- `rwa_proof/THEOREM_T_COMPOSITION.md` (215 lines), `rwa_proof/THEOREM_T_AUDIT.md` (107 lines).
- `helium_research/helium_method.md`, `helium_research/lower_bounds.md`, `research/analytic.md`.
- `gaussian/certified_interval.py` (504 lines), including arithmetic, transcendental enclosures, and self-test definitions.
- `rate_decision/control_expanding/run.py`, `fixed_shift.py`, `certify.py`, and `rate_decision/INDEPENDENT_AUDIT.md`.
- `CORRECTION_PROTOCOL.md`.

`RWA_REPORT.md` was read for its claims and dependency routing; its independent analytic proof audit is outside this subreport. The E2 matrix and rational-trial JSON files were read and used for the bounded replay. Theorem C's detailed argument was read, but its all-order source hypothesis is not re-certified here; it belongs to the analytic/literature audit. Numerical data for other candidates and all historical certificates were not re-executed by this subtask. Source `run.py` was inspected, never called: its cache-generation functions can write beside their source. The new verifier imports only `helium/hylleraas.py`, after setting `sys.dont_write_bytecode=True`, and writes exclusively beside itself under post-freeze work.

## Exact continuum meaning and the two-electron branch

The model in the source is the actual spin-independent, infinite-mass atomic operator

\[
H_{2,Z}=-\tfrac12(\Delta_1+\Delta_2)-Z/|x_1|-Z/|x_2|+1/|x_1-x_2|
\]

on the antisymmetric subspace of \(L^2(\mathbb R^6;\mathbb C^4)\), with spatial domain \(H^2\) intersected with that subspace. Antisymmetry permutes position and spin together. The sliced Hardy inequalities and relative bound quoted in the source imply the claimed domain and graph-norm equivalence by Kato–Rellich. These remain analytic foundations requiring formalization; a rational matrix cannot supply them.

The separator argument is correctly about the full fermionic spin space. The one-electron 1s eigenspace has spatial dimension one and spin dimension two. Its two-electron exterior square has dimension one. Using the next hydrogen energy gives

\[
H_{2,Z}\ge -Z^2P_0-\frac{5Z^2}{8}(I-P_0).
\]

The normalized 1s product times the unit spin singlet has mean \(U_Z=-Z^2+5Z/8\). Thus \(g_Z=\beta_Z-U_Z=Z(3Z-5)/8>0\) for integer \(Z\ge2\). A two-dimensional spectral subspace below \(\beta_Z=-5Z^2/8\) would contain a vector orthogonal to \(P_0\), contradicting the form bound. The trial makes this spectral subspace nonzero. Semiboundedness makes its support bounded, so this argument does not require compact resolvent or an unjustified domain step. It is one eigenspace of dimension one.

Strict \(E_Z<U_Z\) also follows as written: equality in the variational principle would make the product an eigenfunction, whereas its action is \((-Z^2+1/u)\chi_Z\). The scalar positivity/rotation/exchange argument is needed separately to identify the positive three-distance wavefunction; it does not repair or replace the full-spin separator. Neither statement transfers to three electrons by reusing the same rank-one projection.

For a unit vector in \(D(H)\), the second moment is \(\|H\phi\|^2\). The source correctly avoids requiring membership in \(D(H^2)\). The spectral polynomial \((\lambda-E_Z)(\lambda-\beta_Z)\) is nonnegative on the actual spectral support. Its integral proves Temple's lower bound with exactly the stated denominator. The interval-safe bound uses separately unfavorable numerator and denominator bounds; no false global monotonicity assertion is needed.

## Dictionary, moments, and rational heights

Electron count is denoted \(N=2\) here. Approximation order is \(n\); the auxiliary source notation `N=n+2` should be read as \(M_n=n+2\) to avoid confusing it with electron count.

The dictionary is exactly

\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\rm sym},
\]

with factorial-scaled symmetric monomials and rational powers of two normalizing each reduced squared norm into \([1/2,2]\). Its overlap and Hamiltonian forms omit the common \(8\pi^2\), and the singlet has norm one. The regularizer is applied in this reduced normalization. This convention is consistent: normalized physical and reduced quotients agree, and the real reduced witness obeys the Gram bound. Real coefficients suffice because splitting a complex vector into real and imaginary parts splits each relevant real quadratic form.

Each nonzero Hamiltonian-action term has each distance exponent at least −1. The apparent twice-lowered powers have vanishing coefficients at the potentially offending low degrees. There are at most 24 contributions per monomial, 48 per symmetric generator, and 2304 primitive terms per squared-action entry. At intersections of collisions, weak second derivatives have at most inverse individual distances; their squares are locally integrable in the three transverse coordinates. The exponential supplies integrability at infinity.

The exact angular recurrence is valid for \(a,b,c\ge-1\), \(a+b+c>-3\). In the inverse-distance branch the endpoint cancellation is retained before integration. In particular,

\[
B(2j,-1)=\pi^2/8-\sum_{k=0}^{j-1}(2k+1)^{-2}.
\]

This uses the classical reciprocal-square identity, which is a real mathematical dependency. All moment values lie in the **rational linear span** of \(1,\log2,\pi^2\). Several old passages call this a field. That terminology is unnecessary and potentially misleading: the arithmetic used only adds these expressions and scales them rationally; closure under multiplying arbitrary such expressions is never required, and no claim of algebraic independence of these constants is needed.

The overlap \(G\) and Hamiltonian matrix \(A\) are rational because including the measure leaves their primitive powers nonnegative. \(Q=\langle H\phi_i,H\phi_j\rangle\) can require \(\log2\) and \(\pi^2\). It is the full action norm, not \(AG^{-1}A\). Unequal exponents enter by their sum only in the integral; each individual action keeps its own exponent.

The explicit height proof has enough slack for the described operation model. With \(D=16M_n\), at most \(D^2\) angular rational summands, denominators at most \(D^3\), radial factorials, factorial-scaled generators, dyadic scaling, and the fixed 2304-term sum give a cubic bound in \(M_n\), with fixed-charge constants. This supports the proposed conservative \(H_Z(n)=2^{40}(z+1)^2M_n^3\). Exact diagonal scaling by a power of four is possible because the target interval has ratio four.

Independence follows by fixing interior angular ratios, applying independence of distinct radial exponential polynomials, and then varying ratios over their open domain. Consequently the rational determinant is positive. If each Gram denominator has at most \(B\) bits, the product of all \(m^2\) denominators clears its determinant, giving

\[
\lambda_{\min}(G)\ge2^{-m^2B}(2m)^{-(m-1)}.
\]

The trace bound uses the prescribed diagonal normalization. Together with \(m\le M_n^4\), this yields an order-11 polynomial coefficient-bit bound. These arguments are independent of RATE. They do not say the floating-point Gram problem is well-conditioned.

## Finite solve, stopping, and cost

The historic global variance minimizer is unsuitable, exactly as the source counterexample demonstrates: it can choose an exact excited vector even when exponentially good ground approximants exist. Its replacement uses the fixed rational shift \(\sigma=-Z^2-1\), with

\[
T=Q-2\sigma A+\sigma^2G+\tau I,\qquad \max_{c\ne0}\frac{c^TGc}{c^TTc}.
\]

The form bound \(H-\sigma\ge I\) gives \(T\ge G+\tau I\). Thus approximate denominator positivity is controlled by \(\tau\), without requiring an oracle for the sign of a transcendental entry. If numerator and denominator operator errors are at most \(e\le\tau/2\), subtracting the two fractions on a Euclidean unit vector gives the stated error at most \(4e/\tau\).

The explicit bisection initialization is adequate. Its lower endpoint is strictly below the approximate maximum, so it has a negative rational witness, and the retained witness remains available at termination. The zero-diagonal branch is valid: for block \(\bigl(\begin{smallmatrix}0&b\\b&d\end{smallmatrix}\bigr)\), the prescribed vector has form value \(b^2(d-2|d|-2)<0\). Positive-pivot Schur elimination and inverse-congruence lifting complete the decision. A zero diagonal row with all zero entries may be deleted.

The resulting normalized reciprocal quotient stays above \(1/(2B_0)\). After \(\|c\|_\infty=1\), this gives \(c^TGc\ge\tau/(2B_0)\), which justifies final interval contraction without unbounded precision search. The mean is exactly rational. An accepted mean \(m\le U_Z\) yields denominator at least \(g_Z\). Each emitted interval is valid subject to the continuum domain, moment identities, and separator, even if RATE fails.

The convergence proof is correctly conditional on an approximation rate for the exact dictionary. The gap turns residual error \(\eta\) into shifted-objective excess at most \(K_Z\eta^2\). The coefficient penalty and additive solve error add \(2\delta_n\). Strict \(U_Z-E_Z>0\) eventually makes the mean filter pass. Unknown analytic constants occur in the mathematical upper bound on the stopping index; they are not numerical inputs to the adaptive algorithm. This distinction makes the described search computable in principle, rather than an oracle-based selection of a noncomputable witness.

Under the declared schoolbook bit model, the paper's conservative counts are internally consistent:

| Component | Bound, fixed \(Z\) |
|---|---:|
| Dictionary generation | \(O(M_n^{16})\) |
| Dimension | \(O(M_n^4)\) |
| Coefficient/required precision exponent | 11 |
| One entry to error \(2^{-s}\) | \(O((M_n+s)^{12})\) |
| All entries at scheduled precision | \(O(M_n^{140})\) |
| Rational PSD solve and contractions | \(O(M_n^{53})\) |
| Successful stage, conditional on exponent \(1/16\) RATE | \(O_Z((p+1)^{16})\) |
| Summed stage costs | \(O_Z((p+1)^{2256})\) |

The common denominator and fraction-free implementation requirements matter: arbitrary repeated rational expression substitution is not the algorithm whose height bound is asserted. Integer intermediate sizes can be bounded by minors and Hadamard; witness recovery can retain a common denominator. No machine-checked implementation or operational cost semantics for this full algorithm was found in these files. The new bounded verifier below also does not establish the all-input operation count.

The literal displayed safe schedule is intentionally impractical. At \(Z=2,n=1\), it already has \(h_n=199449790797450313728\) bits in the exponent defining its denominator precision. This is compatible with a fixed-constant asymptotic theorem but must not be confused with the executed 512/1024-bit finite computations. An executable implementation should use separately proved, much smaller instance-dependent bounds; replacing the schedule needs a new version and its own correctness/cost proof.

## Executed bounded checks

Command from the workspace root:

```sh
python3 -B THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/computation/verify_computation_v1.py
```

Observed Python version: 3.14.7. Exit status: 0. The script used only the standard library. `verification_results_v1.json` records source and script hashes and the exact outcomes:

- 648 nonnegative primitive moments checked exactly against independent positive-octant perimetric binomial integration, with three distinct rational exponent sums.
- 854 rational symmetric matrices checked by the constructive PSD/negative-witness recursion and, independently, all principal minors. Every returned witness had a strictly negative exact quadratic form.
- All 36 independent pairs in the 8-column frozen E2 dictionary checked for overlap and Hamiltonian entries using independent perimetric integration and the first-derivative weak form. Squared-action entries matched the frozen data using the production full-action recurrence.
- The frozen E2 rational trial replayed with independent exact-rational arctangent-series enclosures, using \(\pi=4(\arctan(1/2)+\arctan(1/3))\), and the rational \(\log2\) series. Its outward Temple interval is

\[
[-584161476279/200000000000,\ -362842736637/125000000000],
\]

with exact width \(18065488299/10^{12}\). This checks one finite continuum certificate conditional on the paper analytic premises. It does not certify all inverse-power moments independently, optimize a trial, rerun the original additive LDL certificate, verify RATE, or execute the asymptotic algorithm.

These bounded successes are useful executable evidence and leave all-order proof and Lean obligations explicit.

## Primary-literature comparison and novelty boundary

Harrell's 1978 Theorem 1 states the self-adjoint operator-domain Temple bound; the accompanying remark permits a proved lower separator below the rest of the spectrum. The author-uploaded primary text was inspected, including the spectral-measure argument in Theorem 2 and the overlap statement in Lemma 4. This matches the abstract spectral part of the frozen argument; it does not supply a hydrogenic separator or a Coulomb algorithm. Direct publisher PDF access returned HTTP 403. [Primary author-uploaded text](https://www.researchgate.net/publication/243059969_Generalizations_of_Temple%27s_Inequality).

Nakashima and Nakatsuji (2008), equations (3)–(9) and Table I, use a logarithmic free-complement helium dictionary and numerical variance/modified-Temple bounds. The full four-page primary PDF was inspected. Its excited-state estimate is obtained from a second secular solution; it is not the rank-one full-fermionic separator established above. The paper does not state a directed-rounding arbitrary-precision algorithm with a bit-cost exponent, and its finite convergence table cannot discharge this project's exact-dictionary RATE. Conversely, this project cannot claim novelty for using continuum variance and Temple bounds for helium. [Primary PDF](https://qcri.or.jp/lab/wp-content/uploads/2011/07/p358.pdf).

Bareiss's 1968 primary paper is the standard source for integer-preserving elimination and minor identities. The publisher's indexed primary text and metadata were available; the full direct PDF returned HTTP 403. Only that bounded source access is claimed here. The operational bit estimate above was checked directly from the proposed minor-height argument; no claim that Bareiss states this project's exponent is made. [Primary publisher PDF endpoint](https://www.ams.org/mcom/1968-22-103/S0025-5718-1968-0226829-0/S0025-5718-1968-0226829-0.pdf).

Established components are the spectral method, relative-bound framework, elementary moment integration, rational determinant conditioning, and exact linear algebra. The precise dyadic dictionary together with a global continuum rate and fully tracked fixed-charge precision cost is a candidate combined contribution. This bounded search establishes neither novelty nor priority. Its validity remains dependent on the independent analytic audit, and its full Lean verification remains unfinished.

## Explicit remaining obligations and disposition

1. Discharge the actual continuum global residual RATE for the unchanged dictionary. No arithmetic check establishes it. Retain the full Theorem T as conditional if any analytic premise is unresolved.
2. Formalize the domain, self-adjoint realization, spin permutation space, exact hydrogen gap, full-fermionic separator, and spectral-measure Temple step in Lean. These are not consequences of scalar `#print axioms` results.
3. Formalize the exact trial synthesis and weak derivatives, primitive integrals (including reciprocal-square and logarithm identities), normalization, and all-order coefficient/height bounds.
4. Implement the proposed arbitrary-precision rational search and prove its output specification, finite stage termination, eventual stopping under RATE, and binary bit-cost semantics. Finite fixed-tolerance scripts and noncomputable existence results are distinct artifacts.
5. Keep electron count \(N\) separate from order \(n\), and prove new multi-electron symmetry, separator or alternative certification results. Nothing in this report supplies an \(N=3\) rate or uniform efficiency as \(N\) grows.

No new sealed erratum is proposed by this subreport for a substantive arithmetic falsehood: none was found in the composition inspected. The misleading word “field,” the overloaded `N=n+2`, and the separation of paper algorithm from executable verification deserve a versioned clarification. Any analytic failure discovered by the other audits must receive its own frozen-hash erratum and propagate to this conditional conclusion; an earlier PASS label supplies no evidence against such a failure.
