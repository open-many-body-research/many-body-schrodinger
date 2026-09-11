> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent analytic support review of the OPEN approximation frontier

Date: 2026-09-10. This is a new supporting review for the parent review,
not the canonical requested OPEN-lemma verdict. Evidence category:
**paper proof review of an explicitly conditional approximation theorem**.
No Lean theorem, build, physical numerical certificate, or implementation
was produced in this review. Frozen and successful continuation artifacts
were read without modification.

The reviewed implication is E0 of `ENDPOINT_ONE_THIRD_v3.md`: for fixed
Z >= 2 and a real, normalized, rotationally invariant, exchange-symmetric
physical function satisfying that file's G1, G2, G3,

\[
 V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
 e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\rm sym}(r,s,u),\qquad
 \inf_{v\in V_n^{(Z)}}\|\psi-v\|_{H^2_*}
 \le C e^{-c n^{1/3}}.
\]

Here the norm is the actual six-dimensional Cartesian L2, gradient and
full ordered Hessian norm. The three hypotheses are respectively the
weighted factorial vertex estimate with compatible boundary germs, a
bounded exterior holomorphic germ of radius c/(1+S), and an exponential
physical H2 tail. Constants are for the fixed supplied function and
regularity data; no charge-uniform, geometry-uniform, or computable
constant is asserted by this implication.

**Result of this bounded adversarial check:** the conditional E0 argument
is provable as stated at paper level. No invalid step in E2--E15 was found
after rederiving its degree, overlap, Fourier, polynomial-tail and physical
norm estimates. In particular, no weakening of the exponent 1/3 is forced
by these estimates. This is not a verdict that the full Theorem T, the
Gaussian OPEN lemma, or the complete physical G1--G3 dependency chain has
been formally verified.

## 1. Source reconciliation that matters to this review

The frozen `HELIUM_CERTIFICATION.md` equation (2) asks for a deterministic
polynomial-size *correlated Gaussian* generator for a promised one- or
two-nucleus class, an H1 error, rational parameter heights, and an
exponential bound on the squared coefficient norm. E0 concerns the
different, exact single-nucleus exponential--distance-polynomial space
above, with H2 error and existential coefficients. The two statements
are not interchangeable. No conversion from E0 to that Gaussian
generator is supplied by the inspected files.

The frozen `TWO_ELECTRON_THEOREM.md` is an earlier boundary report:
its abstract RATE-to-cost implication requires added dictionary and
coefficient hypotheses, and its fixed-finite-exponent obstruction does
not apply to E0. In E0 the largest node is Z times 2 to a quantity linear
in n; the exponent set is not fixed as n grows. `RWA_REPORT.md` later
claims the 1/16 rate and cost exponent 2256 for the expanding dictionary.
The endpoint paper keeps that dictionary and degree schedule but supplies
a separate 1/3 approximation construction. Existence of this stronger
approximation does not by itself identify the algorithm that uses it.

The parent review owns the generator, moment, Gram, coefficient-height,
acceptance and bit-complexity reconciliation. This note checks the
analytic construction on which such a reconciliation could depend.

## 2. E2--E5: finite-order extension without hidden factorial growth

For B=m+2, the B probability boxes have total support radius 1/2.
Convolution with the interval [-3/2,3/2] has support [-2,2], takes values
in [0,1], and is one on [-1,1]. Assigning r <= m derivatives to distinct
convolution factors gives total variation at most (2B)^r. At least two
undifferentiated boxes remain, so all the resulting derivatives through
order m are continuous. Their support-boundary jets vanish. The rational
truncated-power formula E2a has the correct shifts and coefficient B^B/B!.
This construction supplies finite C^m regularity, not a nonzero compactly
supported analytic function.

The E4 extension has no factor growing like the number of charts in its
derivative base. With lattice spacing ell=h/16, each support has sup
radius 2 ell. At a fixed point at most 5^3=125 supports are active.
For every inactive cutoff, its value and derivatives through order m
are zero, including boundary points. Consequently the corresponding
factor 1-chi in a telescoping product has only its constant jet there.
The number of factors that actually contribute to a product jet is at
most 125, plus the analytic chart. This remains true for arbitrarily
small h and arbitrarily many total retained charts.

Each cutoff support is within (5/2)ell of its selected point of K,
strictly inside the holomorphic chart and leaving h/2 for Cauchy bounds.
The plateaus cover a real neighborhood of K. Positivity and telescoping
give the zero-order bound M. For derivative order r, the multinomial
sum for at most 126 factors yields

\[
 \|\partial^\nu G_m\|_\infty
 \le125M(126\cdot96m/h)^r,
 \qquad r=|\nu|\le m.
\]

The real-value hypothesis is needed: compatible germs agreeing with a
real F on the full-dimensional real interior of K are real on their
real chart neighborhoods, by uniqueness. No complex F is silently
approximated by a real polynomial.

For composition with 4 cos, Faà di Bruno groups derivatives with the
Stirling numbers S(r,j). Selecting the least element of each partition
block proves the injection bound

\[
 S(r,j)\le {r\choose j}r^{r-j},\qquad
 \sum_j S(r,j)A^j\le(A+r)^r.
\]

For A=4*12096m/h, r<=m and h<=1, this is below
(50000m/h)^r. An additional r! is not required and must not be introduced
in this step; it would change the subsequent optimized exponent.

## 3. E6--E12: all degrees, one polynomial, and the scale dependence

In the high-hq regime set D=floor(q/3) and
m=floor(hD/(4C0)), C0=50000. The threshold in the source implies D>=q/6,
m>=8, m>=hD/(8C0), and C0 m/h<=D/4. Integrating the periodic function
m times in a maximum-frequency direction gives its coefficient bound.
Grouping the at most eight sign choices gives Chebyshev coefficients
bounded by both 8M and 1000M(C0 m/(hR))^m.

There are at most 3(R+1)^2 frequency triples of maximum R. Two algebraic
derivatives of a tensor Chebyshev term cost O((R+1)^4). Thus

\[
 \sum_{R>D}(R+1)^6(D/(4R))^m
 \le64\,4^{-m}D^m\int_D^\infty x^{6-m}\,dx
 =\frac{64D^7 4^{-m}}{m-7}.
\]

The integrand is decreasing for m>=8, so the sum-to-integral comparison
has the right direction. Absolute convergence holds through two
algebraic derivatives. Fourier uniqueness first identifies the value
series, and uniform polynomial derivative convergence then identifies
the derivatives, including at the cube boundary. Truncation has total
degree 3D<=q, not q in each coordinate with total degree 3q.

In the low-hq regime the zero polynomial is legitimate only because the
statement retains h^-2. Cauchy's bound is 2M h^-2, while the chosen
exponential is at least 1/256. This covers all q, including q=0.

The same nonzero Q has at most (q+1)^3 Chebyshev coefficients, each
bounded by 8M. Its cube C2 norm is therefore at most CM(q+1)^7. There is
no appeal to the compact support of G_m when estimating Q away from K.
For completeness, the exterior Chebyshev estimate can be proved with
constants independent of the degree: the recurrence gives
|T_j(z)| <= (1+2|z|)^j for complex z. Applying Cauchy on radius j^-2
about a real point gives, for i<=2 and j>=1,

\[
 |T_j^{(i)}(z)|\le i!e^2j^{2i}(1+2|z|)^j.
\]

The j=0 case is immediate. Rescale z=y/4; for nonnegative coordinates
bounded by t=S(y) and t>=2, 1+t/2<=t. Tensor multiplication, total degree
<=q, and the coefficient count imply the conservative (6t)^q bound E7.

The uniform rescaled data E11 also have the stated powers. Near the
vertex the factorial estimate is invariant after dividing the target
by tau^sigma. At scales bounded below, the exterior radius becomes
c/[tau(1+2tau)] after y=x/tau, so tau<=T permits a common radius
c_h(1+T)^-2. The amplitudes tau^-sigma are bounded on this second range.
The h^-2 cost becomes (1+T)^4; it does not enter an exponential in T.
Thus E12 is the error exp(-b' q/(1+T)^2) times a polynomial prefactor.

## 4. E14--E15: actual polynomial tails and physical H2

Writing k=J=256(q+1), the highest node is j=J+1 and the polynomial
degree is at most k+q. Hence the exact native index is
k+q+2(J+1)=769q+770. No auxiliary cutoff is present in this vector.
The constant term uses the same outer node as the shell sum, so exact
telescoping leaves the outer omitted target psi, not psi-psi(0).
This cancellation is essential because the latter has a nondecaying
constant exterior part.

For a shell tau and i<=2, the exterior target envelope has the form

\[
 |\partial^i f(\tau y)|
 \le C\tau^{\sigma-i}(1+T)^4t^{\sigma-i+4},\quad t\ge2.
\]

Window derivatives of order l contribute at most
C(k+1)^3 tau^-l t^(3-l) exp(-k I(t)). Combining Leibniz terms gives a
reduced derivative envelope proportional to

\[
 \tau^{\sigma-i}e^{-kI(t)}
 \big[t^{\sigma-i+7}+(q+1)^4t^3(6t)^q\big].
\]

The largest squared physical volume power comes from S^5 F0^2:
it is t^(19+2sigma), bounded by t^21 since sigma<1. The polynomial
term needs only t^11, and Hessian and inverse-distance terms have lower
powers. This explicitly verifies the conservative exponent 21 in G16.
The tail integral is

\[
 \int_2^\infty t^{21}(t/2)^{2q-2k}\,dt
 =\frac{2^{22}}{2k-2q-22},\qquad k>q+11.
\]

Taking its square root, the growing coefficient 12^q is dominated by
exp(-k/4) when k=256(q+1), with ample margin for exp(-k/16).
This is a tail estimate for the actual polynomial in the witness.
On lower tails, (4t)^(k/2) absorbs the inverse powers from two
derivatives and the vertex weight; replacing it by a constant small
exponential before the integrations would not justify removability.

Under S=tau t, the zero-, first-, and second-order norms scale as
tau^(sigma+3), tau^(sigma+2), tau^(sigma+1), respectively. The necessary
common bound is tau^(sigma+1)(1+tau^2). The inverse-distance Hessian
term has the same second-order scale. Summing the dyadic scales costs
at most C_sigma(1+T)^4. This verifies the E15 prefactor
(k+1)^3(q+1)^11(1+T)^8 after retaining the older conservative polynomial
factor in q.

The Cartesian norm transfer was checked independently again in this
review. For a radial envelope G(S), the relevant angular integrals are

\[
 \int G(S)\,dx=\frac{8\pi^2}{15}\int G(S)S^5\,dS,
\quad
 \int G(S)r^{-2}\,dx=\frac{16\pi^2}{3}\int G(S)S^3\,dS,
\]

with the same nuclear formula for s and coefficient 16 pi^2/9 for u.
For the last coefficient, the reduced one-dimensional integral is
integral_0^1 v(1-v) log(1/|2v-1|) dv=2/9. Bounded first derivatives
of the distance maps and Hessians of order 1/r, 1/s, 1/u give D11,
with its deliberately loose constant 10^6.

There is no hidden surface delta: for N=2 the three pair collision sets
intersect only at the origin. Fix a removed vertex ball first, send the
pair-tube radius to zero on compact annuli, then send the vertex radius
to zero. Pair boundary areas are O(epsilon^2); compatible reduced germs
bound the first derivatives on those annuli. At the vertex,
g=O(delta^sigma) and grad g=O(delta^(sigma-1)) give first and second
integration-by-parts fluxes O(delta^(sigma+5)) and O(delta^(sigma+4)).
A constant part instead gives the still vanishing O(delta^5) first flux.
The L2 bulk limits follow from D11. Noncollision collinear faces require
no removability argument: all physical distances there are nonzero and
the compatible germ gives an ordinary smooth physical composition.
This N=2 geometry is not an arbitrary-N collision-stratum proof.

Finally, the outer omitted term uses localized Hardy correctly.
The localization chi(S) is bounded Lipschitz, chi psi is H1, and
only first weak derivatives of chi are used. It yields

\[
 \|\psi/r\|_{L^2(S\ge T/8)}
 \le C(1+T^{-1})\|\psi\|_{H^1(S>T/16)}.
\]

The same estimate holds for s. No derivative of a sharp region indicator
is taken and no H2 membership of this Hardy cutoff is required. The
actual dictionary multiplier has bounded first and second scalar
derivatives and its physical Hessian is treated with these Hardy bounds.

With T=(q+1)^(1/3), the fitting exponent q/(1+T)^2 and the physical
tail exponent T both have size q^(1/3). The prefactor has power 50/3
and is absorbed into exp(-c q^(1/3)). The inner and Poisson errors decay
exponentially in q. The stated index conversion and zero approximants
for finitely many small n give all n. This establishes the conditional
rate without taking a singular limit in a Gevrey parameter.

## 5. Counterexamples to tempting weaker premises

These are not counterexamples to E0. They identify precise restrictions
that the reviewed proof needs and actually retains.

1. **Omitting h^-2 in E6 at small degree fails.** Take
   F_h(a,b,c)=cos(a/h), real on K. On every complex h-polydisc its
   modulus is at most cosh(1), independently of h. For q=0 every
   polynomial approximant is constant, so at (0,1/2,0) its second-a
   derivative error is h^-2. A bound CM(q+1)^7 exp(-b hq) without
   h^-2 is therefore false uniformly in h. The actual E6 retains it.
2. **Equality just on the normalized surface does not glue ambient
   germs.** The holomorphic functions 0 and a+b+c-1 agree on
   a+b+c=1 but differ on every full ambient neighborhood. The inspected
   distance gluing lemma correctly requires equality on a full
   three-dimensional real physical intersection, including radial
   neighborhoods. Equal-radius or variable-radius convex overlaps
   then contain a real open physical set and the identity theorem
   applies.
3. **G1 and G2 do not establish an exponential tail.** The normalized
   physical function C(1+S)^-4 is H2, symmetric and rotationally
   invariant. It has the required local weighted bounds and bounded
   exterior analytic germs. Its L2 tail is of order R^-1, not
   exponential: integrate S^5(1+S)^-8. It is not asserted to solve
   the Coulomb eigenvalue equation. It shows why G3 or its eigenfunction
   decay dependency cannot be silently dropped.
4. **Smoothness plus nonvertex analyticity is not weighted analytic
   uniformity.** Near S=0, set
   g(S)=exp(-1/S^2) sin(exp(1/S)), with g(0)=0. Every fixed real
   derivative tends to zero at the vertex, and g is real analytic
   for S>0. For any fixed small delta>0, on z=S(1+i delta) choose a
   sequence S tending to zero such that the imaginary part of 1/z
   is pi/2 modulo pi. Then |sin(exp(1/z))| grows like the exponential
   of exp(c/S), defeating exp(O(S^-2)). A uniform factorial bound
   would imply a bounded holomorphic neighborhood of radius c' S
   by its Taylor series, a contradiction. This illustrates the
   need for the actual uniform PDE recurrence rather than qualitative
   smoothness. It is not a physical PDE counterexample.

No formal Fock series is required by E0. The inspected actual-eigenfunction
composition subtracts kappa*psi(0)*q*log(r^2+s^2) for any fixed real kappa
and proves only the weight S^(1-order). That weight absorbs a quadratic
logarithm for any such coefficient; it does not identify the physical
Fock coefficient or prove a more regular extracted remainder. On a
normalized shell r^2+s^2 is bounded away from zero, so a fixed branch of
its logarithm is available; epsilon^2 |log epsilon|=O(epsilon) controls
the scale factor. This is consistent with higher logarithmic terms and
does not assume convergence of a physical infinite Fock expansion.

## 6. Physical input review boundary and remaining obligations

The actual local/exterior composition files and the boundary-germ lemma
were read directly. Their coordinate changes distinguish the perimetric
sum a+b+c from S=r+s, use a positive spectator length at pair axes,
and handle zero triangle height by an SO(2)-invariant analytic series
in the squared transverse radius. An inverse square root is used only
in the interior with an explicit positive height lower bound. The
exterior construction selects the shortest separation, retains a
radius proportional to 1/(1+S), and glues on full real neighborhoods.
No new coordinate defect was found in these passages.

The H2 tail transfer was also read: it derives its derivative tail from
an actual H2 eigenfunction and an exponential L2 tail using Hardy,
Fourier graph bounds and two radial cutoffs. Its loss gamma/sqrt(N)
is explicit. It does not prove the L2 tail input or binding.

The load-bearing weak KS removability, H12 initialization, factorial
recurrence and quantitative descent modules remain their separately
identified paper dependencies. Their entire operator arguments were
not re-audited or rebuilt during this bounded approximation review.
Existing review agreement is not substituted for their proofs, and
this note does not promote the actual physical G1--G3 conclusion to
kernel verification. The exact bottom-of-spectrum ground state,
symmetry and decay inputs still require their own verified connection
in a fully formal Theorem T.

The construction controls real coefficient magnitudes in its
Chebyshev representation, but its coefficients depend on the unknown
physical function and analytic charts. There is no executable chart
oracle here. Finite elementary cutoff checks do not prove all-order
approximation, rounding stability, interval validity, termination, or
bit complexity. These remain separate from the conditional result
checked in this note.

## 7. Exact source hashes and preservation

Frozen root: `THEOREM_T_FREEZE_2026-09-09_212604/`.
Commit: `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`.
Annotated tag: `theorem-t-proof-freeze-2026-09-09`.
Continuation root: `THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/`.
All following continuation paths are relative to its `audits/` directory.
Hashes were computed from the actual bytes on 2026-09-10.

| Source | SHA-256 |
|---|---|
| Frozen `HELIUM_CERTIFICATION.md` | `a29ba0101875bb621aba3ad954891502e4c8b3dd613ee1634197459fab052d44` |
| Frozen `TWO_ELECTRON_THEOREM.md` | `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79` |
| Frozen `RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` |
| Frozen `rwa_proof/DYADIC_REMAINDER_ATTEMPT.md` | `bb30295c982758a93237b583a6d52d3490c49b0d8f0737036faa4e701d997b02` |
| Frozen `rwa_proof/GLOBAL_DYADIC_ATTEMPT.md` | `b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b` |
| `ENDPOINT_ONE_THIRD_v3.md` | `cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a` |
| `ACTUAL_EIGENFUNCTION_RWA_AND_APPROXIMATION_v1.md` | `40b9492a1e7c3f8d6e82a85dad977135cc03b6b89cd320f152e81367b12de696` |
| `ACTUAL_EIGENFUNCTION_APPROXIMATION_ROOT_REVIEW_v1.md` | `b2d3f1625bfe31a07afd1bb01b99423c112b4a0443e4edbe9155c80a9ad2593a` |
| `PHYSICAL_LOCAL_DISTANCE_ANALYTIC_v1.md` | `8e65d5d7053012e7b40d891f9a310794aa446f87dde902770a9c13ffe4635f3e` |
| `EXTERIOR_DISTANCE_ANALYTIC_v1.md` | `e6fdf92081e37aadd515d7badc65bf632ccfead811b388fc148d169b31183360` |
| `DISTANCE_BOUNDARY_GERMS_v1.md` | `b956af4f732085ae83eb9ace3a965a59ca18bd85e922178f3453f58748c86991` |
| `COULOMB_H2_TAIL_TRANSFER_v1.md` | `c518ebc59a4ad2d533bbc7d967bac1e1d536787f4312960294dd079640ceeaf6` |
| `ENDPOINT_ONE_THIRD_INDEPENDENT_REVIEW_v1.md` | `e80dcf3ab9269fb0db240964fdcce50d362709d80400d37d15aa2e31abb4fc56` |

The earlier endpoint independent review was read only after the present
E2--E15 calculations. A second reviewer independently rederived D11,
G16, the collision flux limits and localized Hardy during this review;
its agreement is supporting evidence, not a proof foundation. No new
external literature claim or novelty claim is made.
