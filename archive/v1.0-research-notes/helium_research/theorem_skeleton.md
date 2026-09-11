> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# A conditional polynomial-bit theorem with one analytic approximation lemma

This is mathematical planning for the physical class in [tractable_target.md](nogo/tractable_target.md). The selected route for the **uniform theorem attempt** is the H¹ approximation route. The separately executed helium Temple certificate is a validation of a particular continuum state and energy enclosure; it is not an execution of the conjectured uniform algorithm below.

**Status ledger.** The infinite-dimensional bridge and regularization estimates below have complete human proofs in this file, but are not claimed to be Lean checked. The integral identities have direct derivations below. The elementary bit algorithms are **PROVABLE with the supplied implementation sketches**; this document does not supply their code-level operation counts or machine proofs. There is one substantive **OPEN** analytic lemma, stated in §3. Its constants have not been established. Consequently this is a conditional theorem skeleton, not an unconditional polynomial-time helium or molecular solver. The audited approximation papers do not prove §3; see [hp_successors.md](helium_research/hp_successors.md).

## 1. The exact physical problem and uniform constants

Fix rational constants `0<rmin<rmax`, `mu_gap>0`, `mu_ion>0`, and an integer `Zmax>=1`. The inputs are the promised two-electron Hamiltonians with one or two positive integer-charge nuclei specified in §1 of tractable_target.md. In the two-nucleus case the rational separation lies in `[rmin,rmax]`. Let `L` be the binary length of the nuclear input and `b>=1` the requested accuracy index. The operator is the unbounded-space Coulomb Hamiltonian on the full antisymmetric two-electron spin Hilbert space, with operator domain `H²∩H_f` and form domain `H¹∩H_f`. Its simple ground eigenvalue `E` is separated from the rest of the spectrum by `mu_gap`, and from the essential spectrum by `mu_ion`.

Put

    Zbar = 2 Zmax,       B = Zbar²,
    K = 2 Zbar + 1,      C = 8 Zbar² + 1.

For the exact quadratic form `q`, the already derived sliced Hardy and hydrogenic bounds give

    −B <= E <= 0,
    |q[f]| <= K ||f||_H¹².

Here the lower energy bound is the two-electron hydrogenic convex-combination bound, not the weaker bound obtained by estimating all attraction by Hardy. The following additional coercivity estimate is useful. Writing `F=||f||₂`, `G²=||∇₁f||₂²+||∇₂f||₂²`, the total attraction is at most

    2 Zbar F (||∇₁f||₂+||∇₂f||₂)
      <= 2 sqrt(2) Zbar F G
      <= G²/4 + 8 Zbar² F².

The pair repulsion is nonnegative. Therefore

    q[f] + C ||f||₂² >= ||f||₂² + ||∇f||₂²/4.       (1)

The argument applies componentwise to spinors. These constants are uniform in nuclear positions. The operator/domain and spectral facts used here remain paper-theorem dependencies until formalized; no finite Gaussian definition replaces the continuum operator.

## 2. An explicit dictionary type with tractable exact matrix elements

The dictionary type is deliberately restricted to isotropic-in-physical-space correlated Gaussians. A primitive is specified by a rational symmetric positive-definite **2×2** matrix `A` and an arbitrary rational center `s=(s₁,s₂)∈R⁶`:

    g_(A,s)(x₁,x₂)
      = [det(2A)]^(3/4) / pi^(3/2)
        * exp(−sum_(d=1)^3 (x^d−s^d)^T A (x^d−s^d)).       (2)

Here `x^d=(x₁d,x₂d)^T`. Thus `||g||₂=1`, and `||g||_H¹²=1+3 tr A`. This is not an arbitrary positive-definite 6×6 covariance; using general anisotropy would require an additional integration analysis. Arbitrary translations of a fixed Gaussian already have dense span in H¹, so this restriction does not create a completeness obstruction. Density alone supplies no polynomial approximation rate.

For the density assertion, if an H¹ function is orthogonal in H¹ to all translates of a fixed Gaussian, the Fourier transform of `(1+|k|²) fhat(k) ghat(k)` vanishes identically. This product is integrable by weighted Cauchy–Schwarz. Fourier uniqueness and the strictly positive Gaussian transform imply `f=0`. Rational translations suffice by continuity of translations in H¹. Applying the bounded antisymmetric projection and all spin basis vectors preserves density in the fermionic form domain.

Let `P_-=(I−Swap)/2` on the combined spatial and spin variables. Dictionary vectors are

    phi_j = P_-(g_(A_j,s_j) tensor chi_j),

where `chi_j` is one of the four standard two-spin basis vectors. Zero vectors and linear dependencies are allowed. This is an explicit operator-domain construction, and `P_-` is a contraction for both the L² and H¹ norms. Exchange maps (2) to another Gaussian of the same type. The Hamiltonian and these vectors are real in this spin basis. The simple ground state can be chosen real: complex conjugation preserves its one-dimensional eigenspace, and a phase change makes its conjugation eigenvalue equal to one.

For two primitives with parameters `(A,s)` and `(D,t)`, use a different letter `W=A+D` for their summed exponent. Set

    m^d = W^(-1)(A s^d + D t^d),
    xi = sum_d [(s^d)^T A s^d + (t^d)^T D t^d − (m^d)^T W m^d],
    S = [det(2A) det(2D)]^(3/4) / [det W]^(3/2) * exp(−xi).

Completing the square proves `xi>=0` and `S=<g_(A,s),g_(D,t)>`. Differentiation, followed by the Gaussian mean and covariance identities, gives the kinetic matrix element

    S * [3 tr(A W^(-1) D)
         + 2 sum_d (A(m^d−s^d)) dot (D(m^d−t^d))].       (3)

For an electron index `i`, let `v=e_i`, and for the electron-pair interaction let `v=(1,−1)^T`. The corresponding three-dimensional difference coordinate has precision

    kappa = 1/(v^T W^(-1) v)

and mean `z=(v^T m^1,v^T m^2,v^T m^3)`. Integrating the other Gaussian coordinate first and then using the radial Coulomb Gaussian integral proves

    <g_A, |v^T x − R|^(-1) g_D>
      = 2 S sqrt(kappa/pi) F0(kappa |z−R|²),
    F0(y) = integral_0^1 exp(−y t²) dt.                  (4)

For nuclear attraction take `v=e_i` and `R` equal to a nucleus; for repulsion take `v=(1,−1)` and `R=0`. Equations (3)–(4), the charges, and the finite spin/permutation sums give every exact Gram and form matrix entry. All integrals are over the original unbounded space, and no Coulomb cutoff is introduced.

**Elementary computation lemma — PROVABLE with an implementation sketch.** If the rational parameters have bit height at most `h`, with eigenvalues of `A` in `[2^(−h),2^h]`, an entry can be enclosed with absolute error `2^(−s)` in at most

    c_elem (h+s+1)^8

bit operations, for an absolute implementation constant `c_elem`. A proof can use schoolbook integer arithmetic and fixed formulas (2)–(4): rational matrix operations have fixed dimension; square roots use integer square-root bounds; pi uses Machin's arctangent series; negative exponentials use Taylor bounds after discarding terms whose arguments exceed the required precision plus the known prefactor size. For F0 at a large argument `y`, the error from replacing it by `sqrt(pi)/(2sqrt(y))` is at most `exp(−y)/(2y)`. For the remaining `0<=y=O(h+s)` range, integrate the exponential Taylor polynomial; its remainder is bounded by `y^(n+1)/(n+1)!`. Taking `n=O(h+s)` suffices. A common denominator built from the input denominator, `n!`, and `(2n+1)!` keeps the exact Taylor arithmetic at polynomial bit height. Intermediate rounding needs only `O(h+s)` guard bits, or the displayed common-denominator construction can be used directly. This elementary lemma is separate routine analysis, not a second analytic approximation conjecture. The value of `c_elem` must be extracted from the eventual implementation; it is not asserted numerically in this document.

After antisymmetrization, at most a fixed number of primitive-pair integrals is required per entry. Also

    |G_ij| <= 1,
    |A_ij| <= K(1+6*2^h),                               (5)

where `G` is the Gram matrix and `A_ij=q(phi_i,phi_j)` denotes the Hamiltonian form matrix from now on. The second estimate follows from the bounded Hermitian form on H¹ and Cauchy–Schwarz for its representing bounded operator. Thus polynomial parameter bit height also controls matrix magnitude.

## 3. The single OPEN analytic lemma

**Uniform stable correlated-Gaussian approximation lemma — OPEN.** There are specified integers `a>=1`, `d>=1` and a specified deterministic dictionary-generation algorithm `D`, depending only on the fixed physical class constants, with the following property. Given a promised nuclear input `x` of length `L` and `p>=1`, `D(x,p)` outputs dictionary vectors of the type in §2 and an integer `h`, with

    Q = a (L+p+1)^d,
    1 <= m <= Q,       L+1 <= h <= Q,
    construction time <= Q²,

such that each rational parameter has numerator/denominator bit height at most `h`, each exponent matrix has eigenvalues in `[2^(−h),2^h]`, and **there exists** a real coefficient vector `c_*` with

    ||c_*||_ell²² <= 2^h,
    ||sum_j (c_*)_j phi_j − psi||_H¹ <= 2^(−p),          (6)

for a normalized real ground state `psi`.

The algorithm sees the nuclear input and resolution only. It is not supplied with the ground state, its energy, its smoothed expansion, or its coefficients. It must output a polynomial-size dictionary; enumerating all rational Gaussians of height `h` does not meet this requirement. The coefficients in (6) need only exist; the finite linear algebra below finds an adequate different vector. In particular the OPEN lemma is an approximation and stability assertion, not an energy-solver oracle or the desired theorem restated as a hypothesis.

Both size/rate and coefficient stability belong to this one approximation property. The stability requirement is essential: a polynomial number of basis functions with coefficients requiring exponentially many **bits** would not prove a polynomial-bit algorithm. The permitted coefficient magnitude `2^h` can be exponentially large in the input/accuracy index, because only `h` bits of scale are required. No Gram condition number is assumed.

At present no explicit `D,a,d` satisfying this statement has been derived. The sources giving local pair-coalescence analytic structure, all-order weighted regularity, or fixed-order algebraic Gaussian approximability do not establish (6), particularly at intersecting collision strata and infinity. This is the single substantive remaining analytic research claim of this skeleton. Calling the dictionary generator “specified” is an obligation of a proof of this lemma, not a generator provided by this document.

## 4. Complete H¹ bridge with regularization instead of a Gram condition promise

Let `Phi c=sum_j c_j phi_j`, `G=Phi*Phi`, and `A` be the exact form matrix. Set

    tau = 2^(−h−2p),
    T = A + C G + tau I.

By (1), for all real coefficient vectors,

    T >= G + tau I >= tau I.                            (7)

Consequently `T` is positive definite even when the dictionary Gram matrix is singular. Define

    lambda = max_(c!=0) (c^T G c)/(c^T T c),
    Ereg = 1/lambda − C.

The vector guaranteed by (6), with `p>=1`, proves that the dictionary is nonzero; hence `0<lambda<=1`. Reversing the quotient proves

    Ereg = inf_(Phi c != 0)
             [q[Phi c] + tau ||c||²]/||Phi c||₂² >= E.  (8)

Write `v=Phi c_*`, `e=v−psi`, and `eta=2^(−p)`. The weak eigenvalue equation cancels the cross terms exactly:

    q[v]−E||v||₂² = q[e]−E||e||₂²
                    <= (K+B) eta².

Also `||v||₂>=1−eta>=1/2`, and `tau||c_*||²<=eta²`. Substitution into (8) gives the explicit continuum error

    0 <= Ereg−E <= Dp,
    Dp = 4(K+B+1) 2^(−2p).                             (9)

This proves the global continuum lower control directly from (6). It makes no assertion about a separate omitted-sector gap. If `Dp<=1`, then `Ereg<=1`, so

    1/(C+1) <= lambda <= 1.                            (10)

This last lower bound is necessary when converting eigenvalue errors into energy errors; perturbing a reciprocal without it would be invalid.

## 5. Complete enclosure algebra and the finite algorithm

Set the total error budget

    epsilon = min(2^(−b), mu_gap * 2^(−2b−1)).

Choose the smallest `p>=1` such that `Dp<=epsilon/4`. This uses `p<=b+c_p`, where, for example, the fixed integer

    H_mu = binary length of the fixed rational mu_gap,
    c_mu = H_mu + max(0, ceil(log2(2/mu_gap))),
    c_p = 2 + c_mu + ceil(log2(16(K+B+1)))

is sufficient. Indeed `epsilon>=2^(−2b−c_mu)`, while
`2c_p>=c_mu+ceil(log2(16(K+B+1)))`; therefore `p=b+c_p` passes the required comparison, and the smallest acceptable `p` is no larger. This explicitly includes the doubled state-accuracy exponent `2b`. Logs here specify integer size bounds; the implementation chooses `p` using exact rational comparisons and powers of two. Define

    theta = epsilon / [64(C+1)²],
    nu = tau theta / [2(C+2)].

Put `s=ceil(log2(m/nu))`. Use §2 to enclose each upper-triangular Gram and form entry in a rational interval of radius at most `2^(−s−2)`. Round its midpoint to the nearest point of the **same dyadic grid `2^(−s) Z` for every entry of both matrices**, and copy the result to the transposed entry. The total entry error is at most `3*2^(−s)/4<=nu/m`. The symmetric matrices `Ghat,Ahat` therefore have respective operator-norm errors at most `nu` and a common denominator `2^s`. This common-grid choice is part of the algorithm, not an assumption about arbitrary rational entries. Set

    That = Ahat + C Ghat + tau I.

Then `||That−T||<=(C+1)nu<=tau/2`, so `That>=tau I/2`. For any nonzero `c`, put `r=(c^TGc)/(c^TTc)` and define `rhat` similarly. Since `0<=r<=1`, subtraction of the quotients gives

    |rhat−r|
      <= [nu + (C+1)nu] / [tau−(C+1)nu]
      <= 2(C+2)nu/tau = theta.                        (11)

The same uniform bound holds for the two maxima `lambdahat` and `lambda`. No positive definiteness of `Ghat` is needed. From (10) and the size of `theta`,

    1/[2(C+1)] < lambdahat < 2.

To enclose `lambdahat`, bisect this rational interval using the exact equivalence

    lambdahat <= t  iff  t That − Ghat is positive semidefinite.

A rational symmetric positive-semidefiniteness test is polynomial bit arithmetic: pivot on a positive diagonal and pass to its Schur complement; a negative diagonal provides a negative witness, while a zero diagonal with a nonzero off-diagonal entry supplies a rational negative vector. Otherwise discard the zero row/column. Fraction-free elimination bounds intermediate numerators and denominators by determinants of input minors. The non-positive-semidefinite case returns a rational vector with a strictly negative quadratic form; back substitution preserves polynomial bit height. This describes a global extremal-eigenvalue test, not a local optimizer.

Maintain an upper endpoint `u` whose matrix is positive semidefinite and a lower endpoint `t` with a rational witness `c` satisfying `rhat(c)>t`. Initially the lower test has such a witness by the strict lower bound above. Stop when `u−t<=theta`. Define

    l = t−theta,       v = u+theta.

Then `0<l<=lambda<=v`, and the retained witness obeys `r(c)>l`. Moreover `v−l<=3theta`; because `lambda>=1/(C+1)`, both relevant positive denominators are at least `1/[2(C+1)]`. Therefore

    1/l − 1/v <= 12(C+1)² theta = 3epsilon/16.

Return the rational interval

    [ell,U] = [1/v−C−Dp, 1/l−C],                      (12)

and the finitely described normalized state

    w = Phi c / sqrt(c^T G c).

The exact Gram form defines this normalization; there is no claim that its square root is rational. Equations (8)–(11) prove `ell<=E<=U`. The witness additionally gives

    q[w] <= 1/r(c)−C < U.

Thus the energy interval and the state use the same rigorous error budget:

    U−ell <= Dp + 3epsilon/16 <= 7epsilon/16 < epsilon,
    q[w]−E < epsilon.

The continuum gap and the orthogonal decomposition `w=z psi+w_perp` yield

    inf_(|phase|=1) ||w−phase psi||₂²
      <= 2(q[w]−E)/mu_gap <= 2^(−2b).

The proof is just `||w_perp||²<=(q[w]−E)/mu_gap` and
`2−2|<psi,w>|<=2(1−|<psi,w>|²)`. This completes the conditional correctness proof, including state preparation as an explicit mathematical description. It is a classical algorithm; there is no quantum state-preparation cost assertion.

A certificate records the rational parameter list, integration intervals, norm-error conversions, rational PSD congruence data and negative witness, and (12). The proof that it encloses the **continuum** energy still depends on the global analytic lemma (6). A replayable rational certificate does not make that unproved lemma true, and does not itself formalize the analytic integral identities.

## 6. A traceable polynomial bit bound

This section provides a deliberately conservative operation budget in terms of the named OPEN-lemma constants `a,d` and elementary implementation constants. It does not assert an unconditional numerical constant.

Put `c_C=ceil(log2(C+2))` and

    S0 = c_mu + 3c_C + 16,
    B0 = 4S0 + 16c_C + 32,
    J0 = c_mu + 2c_C + 10.

Using `m,h<=Q`, `p<=L+p+1<=Q`, `log2(1/epsilon)<=2p` from the choice of `p`, and the definitions in §5, entry precision

    s = ceil(log2(m/nu))

is at most `S0 Q`. The input-height bound (5), the `tau` denominator, and the dyadic bisection endpoints give PSD test matrices with rational-entry bit height at most `B0 Q`. The number of bisections is at most `J0 Q`. These inequalities have slack to cover endpoint encodings and symmetrization.

More explicitly, put `s0=max(s,h+2p)`. Because `C` is an integer and `tau` is dyadic, `That` has common denominator `2^s0`. Starting bisection at `1/[2(C+1)]` and `2` means that after `j` bisections every endpoint has denominator dividing `2^(j+1)(C+1)`. Consequently each PSD test matrix has a common denominator dividing

    2^(s0+j+1) (C+1).

Its integer numerators and this denominator have the stated `B0 Q` height bound. Let `c_psd` be an implementation constant such that a rational symmetric `m×m` PSD test **in this common-denominator representation**, including a negative witness when appropriate, costs at most

    c_psd m^5 (Bentry+ceil(log2(m+1))+1)²

bit operations. The bound follows from `O(m³)` fraction-free rational operations, determinant-controlled intermediate bit height `O(m(Bentry+log m))`, and schoolbook multiplication/division. Extracting an explicit `c_psd` from code is a routine PROVABLE implementation obligation. In particular no eigenvalue-separation or Gram-conditioning constant is hidden in this cost.

After increasing the two universal implementation constants to absorb fixed permutation sums and elementary formatting, matrix assembly and all finite algebra cost at most

    C0 Q^10,
    C0 = 1 + 16 c_elem (S0+2)^8
             + c_psd J0 (B0+3)² + c_out,

where `c_out` is the fixed implementation constant for certificate assembly and output. The powers arise transparently: `m²` entries times `(h+s+1)^8` gives `Q^10`; `Q` PSD tests times `m^5` times squared entry height gives at most `Q^8`; dictionary generation and output are lower powers. The returned rational witness has polynomial bit height by the same minor determinant bounds.

Since `p<=b+c_p`, the final conditional bound is

    cost <= C_total (L+b+1)^P,
    P = 10d,
    C_total = C0 a^10 (1+c_p)^(10d).                  (13)

This is a formula for the cost exponent and constant **if** the OPEN lemma supplies explicit `a,d,D` and the elementary implementations supply `c_elem,c_psd,c_out`. No such unconditional numerical values are claimed. The ionization and geometry constants enter through `a,d,D`; the spectral gap also enters the explicit `c_mu,c_p`. The proof remains a theorem skeleton until the labelled elementary implementation obligations are discharged.

For a bounded observable `O` with `||O||<=1`, the state bound gives expectation error at most `2^(1−b)`. To compute an expectation, provide a matrix-element interface with its own polynomial bit bound. A concrete example is a rational Gaussian density probe `(exp(−a|x₁−y|²)+exp(−a|x₂−y|²))/2` with bounded positive rational `a` and bounded rational `y`; its matrix entries follow from another completed square. Its input length must be included in the cost. Arbitrary unspecified observables and unbounded energies/forces are outside this interface.

## 7. Why this route is preferable to adding Temple to the uniform theorem

For the particular helium Hamiltonian, the second fermionic min-max level of the noninteracting charge-two hydrogen sum is `−5/2`. Electron repulsion is nonnegative, so the full second min-max level is at least

    beta = −5/2.

A rational Hylleraas trial vector in H² with mean `a<beta` and residual variance `sigma²` gives the rigorous continuum enclosure

    a−sigma²/(beta−a) <= E <= a.

The hydrogen spectral theorem, min-max comparison, domain justification, integral formulas, and residual certificate must be proved separately; this is carried out or explicitly tracked in the helium validation work. This is a particularly useful **a posteriori** certificate because its lower endpoint does not assume a convergence rate.

However, a uniform polynomial-bit theorem based on Temple would additionally need a constructive global graph-norm approximation rate and efficient certified residual integrals. Ordinary H¹ finite elements are not automatically in H². For general two-center systems, a promised spectral gap does not supply an absolute separator `beta`: a tiny residual could belong to an excited state. An independently certified coarse ground-energy enclosure `[ell0,u0]` of width below `mu_gap/2` would give `beta=ell0+mu_gap>u0`, but deriving that coarse enclosure still needs a constructive global lower-bound argument. Known positive trial overlap without a quantitative ground-state overlap bound does not repair this problem.

The H¹ bridge (9) uses the single stated approximation lemma to supply the continuum lower bound directly. It requires only Gram and Hamiltonian form integrals, removes Gram conditioning by (7), and avoids a separate spectral-separator construction. The helium Temple calculation should therefore be reported as an independent certified benchmark and evidence about posterior enclosures, not as an implementation of the uniform algorithm (6)–(13).

## 8. Exact mapping to A–D and the remaining theorem

* **A, effective global H¹ approximation:** precisely the error assertion in OPEN lemma (6).
* **B, polynomial construction and size:** precisely the dictionary/bit-height part of the same OPEN approximation lemma. It must supply an actual generator independent of the unknown eigenfunction.
* **C, certified integration and adequate precision:** direct Gaussian formulas plus the elementary computation lemma; the regularizer and coefficient stability replace an assumed Gram condition number.
* **D, a certified global finite solve and near-optimal vector:** exact rational PSD bisection, its negative witness, and (11)–(12). The polynomial cost proof is the labelled elementary implementation obligation.

The single most important theorem to prove or refute for this selected route is the **uniform stable correlated-Gaussian approximation lemma of §3**, with an explicit dictionary generator and explicit `a,d`. Refuting that particular lemma would refute this route, not every possible polynomial-time algorithm for this physical class. Proving it, together with the routine computational lemmas whose sketches are given, would establish the conditional algorithm as a genuine restricted-class result; it would neither characterize all tractable Coulomb classes nor address growing electron number.
