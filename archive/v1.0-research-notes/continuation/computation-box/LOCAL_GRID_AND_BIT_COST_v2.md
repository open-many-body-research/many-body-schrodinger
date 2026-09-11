> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local node grids and an operational bit bound, v2

This is a separate algorithmic version of `general_box_enclose_v1.py` and
`atomic_enclose_v1.py`. Its energy target, Dirichlet sine space, spin occupations,
clipping, complement argument, and full-space IMS recursion are unchanged.
Only the grid used to compute each cached integral changes. The mathematical
evidence is a paper proof plus exact-rational execution and replay. None of this
document or the Python implementation is a Lean or kernel verification.

## 1. Exact contract and local grid correction

Inputs are integers N>=0, Z>=1, p>=1. The atomic output encloses the spectral
infimum of the continuum, full fermionic spin-space Hamiltonian
H=-1/2 sum_i Delta_i - Z sum_i |x_i|^-1 + sum_(i<j) |x_i-x_j|^-1,
with width <=2^-p. The paper continuum foundation, form/operator connection,
and unattained-infimum localization argument are exactly those identified in
`ATOMIC_REQUESTED_PRECISION_v1.md` and `GENERAL_BOX_REQUESTED_WIDTH_v1.md`.
No binding, ground-vector selection, spectral gap, or attainment is assumed.
The primitive box input is a rational R>=1 and rational 0<epsilon<1 on
(-2R,2R)^(3N), with Dirichlet form domain and the same output target.

Let K be the complete orbital cube cutoff, m=binom(2K^3,N), and J0 the
minimum grid prescribed by the v1 scalar schedule. A nuclear integral uses two
spatial orbitals, hence at most six scalar indices from 1,...,K. A pair integral
uses four, hence at most twelve. For each canonical cache key, take the LCM L
of **only those indices**, and set J=L ceil(J0/L). Then

    J0 <= J < J0+K^6       (nuclear),
    J0 <= J < J0+K^12      (pair).

Every sine zero remains on a cell boundary. The canonical real integral key
fixes one grid for all its permutations, so nuclear symmetry, pair exchange,
and Hermitian matrix assembly remain valid. There is no requirement for two
different matrix integrals to use the same partition. The spatial estimates
only use J>=J0. For each fixed input all local grids are fixed before their
interval arithmetic precision is refined.

This removes a real inefficiency: v1 forced every grid to be a multiple of
lcm(1,...,K), which is at least 2^K/(K+1). The elementary lower bound follows
because each binomial(K,j) divides that LCM: for every prime, the valuation of
the binomial is a sum of at most floor(log_prime K) terms, each at most one.
Their maximum is at least the average 2^K/(K+1). This was a cost obstruction,
not a correctness defect in the sealed v1 certificates.

The sources are `occupation_box_stage_v2.py`, `general_box_enclose_v2.py`, and
`atomic_enclose_v2.py`, using the unchanged, signed
`general_sine_integrals_v1.py`. As in the repaired v1 program, the new entrypoints
disable the Python integer decimal-conversion cap before parsing or emitting
proof data. See `ERRATUM_INTEGER_CONVERSION_LIMIT_v1.md` for the preserved
counterexample and exact limits of that correction.

## 2. Explicit acceptance precision

Here is a deliberately loose quantitative replacement for the earlier
fixed-grid convergence argument. Write u=2^-b, J*=J0+K^12, and let e=epsilon/32
be the accepted matrix row-radius budget. All clipped schedule parameters have
M>=1, R>=1. Define

    A = 2^20 m (N+1)^2 (Z+N+1) (M+1)^2 (J*+1)^6 (K+1)^2.

It suffices to have b>=32 and

    2^-b <= min(e/(4A), 1/(2M), 1/(4096 J*)).

`precision_cost_bound_v2.py` evaluates the smallest integer satisfying these
displayed inequalities, or 32 if larger. The doubling loop therefore accepts
no later than the first precision 32*2^j above that bound. This is a guaranteed
sufficient precision, not an estimate of the first precision that will pass.

For completeness, the elementary endpoint estimates behind A follow. An
"endpoint excess" is the maximum displacement of either computed endpoint
from the corresponding endpoint of the same finite-grid formula evaluated
with exact real sine masses and exact clipped inverse-distance extrema.
It measures arithmetic uncertainty separately from actual cell variation.

* The Machin interval called at b+8 has width at most u/512 and lies in (3,4).
  For `sin_pi` the reduced argument lies in [0,2] with width at most u/1024.
  The sum of absolute derivatives of all its odd Taylor terms is cosh(2)<4;
  the added remainder has width at most u/8. Thus each returned sine interval
  has width <u/4. The normalized one-dimensional overlap formula divides
  nonzero frequencies by |h| pi>=3, while its sine-difference magnitude is
  <=5/2. Its interval width, including final dyadic rounding and the two
  primitive differences, is <=8u. Intersecting a known sign with [0,infinity)
  does not increase endpoint excess. Exact absolute cell masses are <=1, so
  their computed upper endpoints are <=2 under the displayed assumptions.
* A dyadic square root has error <=u. At an unclipped distance r>1/M, u<=1/(2M)
  implies its lower endpoint is >=r/2. Taking reciprocals therefore adds at
  most 2M^2 u of endpoint error. Including outward dyadic rounding, the
  inverse-distance range has excess <=3(M+1)^2 u. Its upper endpoint is at
  most M+u, because the code saturates the inverse at M before rounding.
  At a clipped distance, including zero, the representative is exactly M.
* Each one-axis positive or negative difference mass sums at most J products.
  The interval width of one product is <=32u, hence that sum has width
  <=32Ju. Its exact value is <=1: sum_j |mass_j| <=1 by Cauchy-Schwarz,
  and the restricted convolution is bounded by the full product of those
  sums. The upper endpoint is <=2 since 32Ju<=1/128.
* Each three-coordinate positive or negative mass is a sum of four products
  of three such one-axis masses. A product width is <=3*4*32Ju; summing four
  gives <=1536Ju. Its exact value is <=1 (it is a sign-restricted sum of
  absolute product masses), so its computed upper endpoint is <=2 since
  1536Ju<=3/8. Multiplying by the inverse-distance interval, summing at most
  J^3 groups with reflection multiplicity <=8, subtracting the negative
  group and rounding gives a pair-integral endpoint excess bounded by
  2^15 J^4(M+1)^2 u. A nuclear mass is one product of three cell masses;
  the same argument gives the smaller bound 2^10 J^3(M+1)^2 u.
* One kinetic spin-orbital interval has excess <=2(K+1)^2 u, using R>=1,
  pi<4 and the final dyadic rounding. A fixed determinant matrix entry has
  <=N one-body contributions and total absolute two-body coefficient count
  <=N(N-1), as proved in the v1 requested-width document. Consequently its
  arithmetic endpoint excess is at most

      [2^10 NZ J*^3(M+1)^2 + 2N(K+1)^2
       + 2^15 N(N-1) J*^4(M+1)^2 + 1] u.

  The final +1 covers one last outward dyadic rounding. Taking the Hermitian
  intersection cannot increase endpoint excess, because max and min are
  1-Lipschitz for the supremum norm on pairs of endpoints. Multiplying the
  displayed entry bound by m is bounded by A, term by term.

The exact finite-grid matrix has row radius <=e/4 from the unchanged spatial
budget J0>=4D/(e/m), D=4RM^2[NZ+2N(N-1)]. Its computed row radius is therefore
<=e/4+A u<=e/2<e. This proves the stopping assertion with a strict margin.
Earlier attempts at lower b cannot invalidate correctness: every primitive
encloses its target at every positive precision, and the actual error is
checked before acceptance.

## 3. Operational bit model and operand sizes

Use a deterministic binary integer model, with explicit costs for addition,
multiplication, division, gcd, and integer square root. Schoolbook algorithms
give polynomial bit cost for all these operations; rational arithmetic uses
integer numerator and denominator pairs reduced by gcd. This is an algorithmic
bit bound, not a benchmark promise for a specific Python/C library build.
The implementations of Python integers, Fraction, math.isqrt, JSON, and the
runtime are part of the disclosed computational trust boundary.

For a finite stage let L=2K^3, let q be its number of PSD bisections, and let s
bound b plus the binary lengths of N,Z,R,M,K,J*, and the tolerance and other
rational inputs. Numerators and denominators of rational inputs are both
counted. For a general box these input lengths must not be omitted.

The Machin series takes O(b) terms. Without relying on cancellation its
accumulated rational denominators have O(b^2) bits. A sine Taylor evaluation
takes O(b) terms since the reduced argument is <=2; elementary factorial
bounds suffice. Its powers, factorials and rational sums have polynomial
operand size in s (O(s^5) is a conservative bound). Thus all overlap and
inverse-distance primitives have polynomial bit cost; O(s^18) is more than
sufficient with schoolbook multiplication/division and a cubic bound for gcd.
These estimates include computing and reducing the rational angles k*j/J.

After `one_dim_overlap`, its mass endpoints are dyadic with denominator
dividing 2^b. Nuclear sums have a common denominator dividing 2^(4b), and pair
sums one dividing 2^(7b); the intervening sums do not acquire unrelated
denominators. They are rounded back to denominator 2^b before assembly. The
selected M,Z are integers; allowing arbitrary rational finite-stage Z would
add its given denominator, not a new one per term. Matrix sums therefore have
polynomial operand length in s+log m. The final real-symmetric midpoint matrix
has a common denominator dividing 2^(b+1).

There are at most K^6 nuclear and K^12 pair spatial integral cache keys. Each
integral uses O(J*^3+J*^2) exact interval updates and O(J*) one-dimensional
overlap requests. Assembly executes O(m N L + m N^2 L^2) creation/annihilation
attempts, each using O(N) operations on orbital index tuples. It stores m^2
interval entries. The one-dimensional memo table has at most O(K^14 J*)
keys: at most K^12 grid choices, K^2 frequency pairs and J* cells. Other tables
have at most O(m+K^12) entries. Even allowing a linear scan of a full table
for every hash lookup gives a polynomial bound in K,m,J*,N,s, so no unit-cost
hashing or favorable average hash behavior is needed for this conclusion.

For an explicit loose bound one can take construction cost

    O(Q H (s+log m)^18),
    Q = (K+1)^12 (J*+1)^3 + (m+1)(N+1)^3(L+1)^2 + (m+1)^2,
    H = (K+1)^14(J*+1) + (m+1) + (K+1)^12.

This deliberately charges every arithmetic update the maximal table-lookup
factor. It is not intended to predict observed timings.

For PSD, each shifted midpoint matrix again has a common denominator, now
dividing 2^(b+1+q). After that rescaling its entry bit length is O(s+q+log m).
Every Schur entry is a ratio of minors of the original shifted matrix.
Hadamard's determinant bound gives O(m(s+q+log m)) operand bits, including
the temporary products before Fraction reduction. This common-denominator
condition is essential; it would be false to infer the same bound from only
an entrywise size bound for arbitrary unrelated rational denominators.
Each decision makes O(m^3) rational updates, hence costs at most
O(m^6(s+q+log m)^3) in the conservative integer model. There are q decisions,
with

    q = O(1 + log2(1 + m(Tmax+B+e)/tau)),
    Tmax = 15 N K^2/(16 R^2),  B=M[NZ+N(N-1)/2].

This follows from Gershgorin's initial interval and exact halving; it counts
operand growth rather than treating a rational comparison as unit cost.
Serialization, hashing the finite source files, and checking cost no more
than a polynomial in these displayed sizes; a replay repeats the construction.
The arithmetic-precision doubling loop contributes O(log b_sufficient)
attempts. Global one-dimensional and sine memo tables persist across attempts;
allow another factor O(log b_sufficient) in their worst-case linear-scan
lookup cost. A safe total overhead is therefore
O((1+log b_sufficient)^2), without needing geometric-domination assumptions.
Earlier square-root refinements use at most O(log M) bits before
a nonzero lower endpoint is found, also covered by the input-size bound.

## 4. Consequence for fixed atomic inputs

Fix positive N and Z. The bottom-up full-space calls have at most N levels and
effective precision p+3(N-k), which differs from p by a fixed amount. For each:

    R = O_(N,Z)(2^p),       U0,K0 = O_(N,Z)(1),
    M,B = O_(N,Z)(2^p),     K = O_(N,Z)(2^(5p/2)),
    m = O_(N,Z)(2^(15Np/2)),
    J0 = O_(N,Z)(2^((4+15N/2)p)),
    J* = O_(N,Z)(2^(max(4+15N/2,30)p)).

The formula for A now implies b_sufficient=O_(N,Z)(p), and the Gershgorin
formula gives q=O_(N,Z)(p). Every polynomial factor in the finite-stage bit
bound is thus 2^O_(N,Z)(p). Consequently this **paper-supported implemented
construction has a deterministic bit-cost upper bound 2^O_(N,Z)(p)** for each
fixed N,Z in the declared model, including its emitted finite certificate.
N=0 is immediate. This is polynomial in inverse absolute accuracy 2^p with
an exponent depending on N,Z; it is not polynomial in p and does not assert
uniform efficiency as particle count or charge grows. Input p itself is
an integer, so this output-sensitive bound is not polynomial in its binary
input length log p either. All finite-N,Z dependence remains in the explicit
schedule, combinatorial dimensions, precision formula and bit model above.

No positive-N conservative requested-width run is claimed. The local-grid
change removes the extra exponential caused by v1's unnecessary common LCM;
it does not make the huge scheduled matrices practicable. Novelty has not
been established by this implementation or cost analysis.

## Preservation and exact historical boundary

The baseline source is the frozen `TWO_ELECTRON_THEOREM.md`, SHA-256
`7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, under
`THEOREM_T_FREEZE_2026-09-09_212604/`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. The predecessor localization argument is
`AUDIT_2026-09-09_v1/arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`, SHA-256
`18093804ba5070c6ad66767432de1ee04eb76bec52bdbe13ee3e0dfc65f4b1bb`.
The v1 implementation records remain sealed by
`GENERAL_PROGRAM_SEALED_MANIFEST_v1.json`, SHA-256
`4a87f3317c4580e676a75c61b359103b3c7481b093ded3e580029fefddc66343`.
This changed schedule is a separately identified gap-free method, not a proof
of the frozen two-electron trial dictionary, rate 1/16, exponent 2256, or
Theorem T. Full Theorem T and the unfinished Lean continuum obligations retain
their separate unresolved status.
