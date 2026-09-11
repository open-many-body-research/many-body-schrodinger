> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# General requested-width fermionic box procedure

`general_box_enclose_v1.py` composes the implemented full occupation matrix and
signed sine integral routines into an actual rational requested-width procedure
for arbitrary finite N>=0, integer Z>=1, rational R>=1 and rational 0<epsilon<1.
The target is the uncut fermionic Coulomb Dirichlet form infimum on
`(-2R,2R)^(3N)` with all spin components and simultaneous antisymmetry. Classical
operator/spectral identification remains a paper dependency. This is a paper
correctness/termination argument for executable code in an unbounded integer
and finite-array model, **not Lean or compiler/runtime verification**.

No positive-N conservative scheduled call has been executed: those sizes remain
prohibitive. Actual tested positive-N finite stages are separately identified.
N=0 is exactly [0,0] and is executed in regression tests, including a requested
width whose decimal input exceeds the old Python guard.

Frozen provenance: `TWO_ELECTRON_THEOREM.md`, SHA-256
`7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. This separately identified sine/occupation
algorithm does not implement the frozen two-electron dictionary or exponents.

## Explicit common trial and clipping allocation

Find the least integer k0 with `2k0³>=N` by doubling and integer bisection.
Enumerate the first N spin orbitals in its sine cube and let S be their total
index-square sum. This is an explicit normalized Slater state. Its kinetic
energy is `pi²S/(32R²)`, and dropping attraction and bounding pair repulsion
gives a common clipped/uncut variational upper bound

`U0=5S/(8R²)+N(N-1)²/2`,

using pi²<10 and `pair <= T+N(N-1)²/2`. Both forms satisfy
`q,q_M>=T/2-NZ²`. Therefore both minimizing-state kinetic energies are at most
`K0=2(U0+NZ²)`. Put

`rho=eta=epsilon/8`, `e=epsilon/32`, `tau=epsilon/8`,

and choose integer `M>=K0(2Z+N-1)/rho`. The previously proved absolute form
clipping estimate and opposite-minimizer argument give
`|lambda-lambda_M|<=rho`. Compact-domain minimizing sequences also suffice.

## Orbital cube and complement

Let `B=M(NZ+N(N-1)/2)`. Choose K>=k0 using integer square-root arithmetic until

`9(K+1)²/(32R²) >= U0+B+B²/eta`.

The complete P is the N-fold exterior space of all `2K³` sine-spin orbitals,
with dimension `m=binomial(2K³,N)`. It includes the anchor. The actual omitted
kinetic threshold is at least
`pi_lo²*((K+1)²+2+3(N-1))/(32R²)`, hence exceeds the coarse scheduled threshold.
Since `lambda_P<=U0`, the exact P/Q estimate implies

`lambda_P-eta <= lambda_M <= lambda_P`.

This uses no binding, physical spectral gap, nondegenerate ground state, or
identification of a chosen trial with a physical eigenvector.

## Quantitative grid choice for arbitrary matrix entries

Fix K,M first and set `t=e/m`. The clipped inverse-radius function is globally
M²-Lipschitz: it is constant on r<=1/M and has radial derivative bounded by M²
outside, while distance itself is 1-Lipschitz.

For one nuclear cell of side `h=4R/J`, the inverse-radius range has width at
most `M² h sqrt(3)<8RM²/J`. Its limiting integral-interval radius is at most
`4RM²/J` times the cell absolute overlap mass. Summing cells and using
`integral |phi_p phi_r|<=1` gives that same bound for every normalized nuclear
cross entry.

For a pair cell group, the relative coordinate lies in a cube of side 2h, so
the radial range has width at most `2h sqrt(3) M²<16RM²/J`. Keeping positive and
negative groups separately gives limiting integral-interval radius at most
`8RM²/J` times total absolute product mass. That mass is bounded by
`(integral |phi_p phi_r|)(integral |phi_q phi_s|)<=1`.

For a *fixed pair of occupation vectors*, there are at most N contributing
one-body terms: for each occupied annihilation index q, the creation index p
that reaches the specified bra is forced. For two-body terms there are
N(N-1) ordered annihilation pairs. For each such pair, either the remaining
occupation is not contained in the bra, or exactly two missing creation indices
are forced. Their two orders each carry coefficient magnitude 1/2, so total
absolute coefficient weight is at most one per annihilation pair. Thus the
absolute coefficient count is at most N(N-1), regardless of the much larger
number of attempted loops.

Consequently every assembled matrix entry has limiting spatial radius at most

`D/J`, where `D=4RM²[NZ+2N(N-1)]`.

Choose an integer minimum `J_min>=4D/t`, then the least multiple J>=J_min of
`lcm(1,...,K)`. This explicitly resolves every sine node. It is a finite integer
operation. Each entry's limiting spatial radius is <=t/4, hence every row's
limiting radius sum is <=e/4. Real-symmetric interval intersection cannot
increase this bound.

The `plan` command reports scalar parameters and the required LCM expression
without allocating the LCM, basis, grid or matrix. The actual `enclose` procedure
materializes J before beginning integration. A scalar plan is not a completed
numerical enclosure.

## Fixed-grid arithmetic refinement and finite termination

Starting with interval bits=32, compute the entire finite stage at this fixed
J,K,M. Accept only when the **observed rational row-error bound** is <=e;
otherwise double the interval bit precision and recompute.

For the fixed finite grid and orbital set, the Machin, sine-Taylor, square-root,
reciprocal, integrated overlap, dyadic rounding and all finite sum/product
interval errors tend to zero as bits grows. The exact clipped integrands are
bounded. Signed masses use mathematically known cell signs, so narrowing does
not require a numerical sign decision at an unknown zero. Therefore the row
bound approaches a limit <=e/4, leaving a strict margin before e. The bit loop
terminates. This argument fixes the spatial grid first; it does not assume that
jointly increasing grid size and arithmetic precision automatically converges.

Exact rational PSD bisection encloses the midpoint matrix eigenvalue in [l,h]
with width<=tau. With the accepted actual row error e_actual<=e, the returned
interval before optional universal-bound intersection is

`[l-e_actual-eta-rho, h+e_actual+rho]`.

It contains the uncut box energy and has width at most

`tau+2e+eta+2rho = 9epsilon/16 < epsilon`.

All searches, indexing, primitive stopping criteria, eigenvalue decisions and
acceptance comparisons are actual integer/rational procedures. No noncomputable
choice or assumed successful matrix is used. This establishes the paper
algorithm contract subject to the stated source/math trust boundary; it does
not certify its Python implementation in Lean.

## Runtime correction, tests and practical boundary

The new entry point imports `exact_integer_runtime_v1.py` before parsing inputs
or writing certificates. It explicitly disables Python's decimal digit-count
guard. `ERRATUM_INTEGER_CONVERSION_LIMIT_v1.md` records the concrete counterexample
to the earlier default-runtime claim and its repair without editing the sealed
source. The same 10^-5000 request now serializes and roundtrips exactly, producing
227823 JSON characters in the legacy schedule regression. Unlimited decimal
conversion does not promise unlimited physical memory or runtime.

`test_general_box_enclose_v1.py` passes exact scalar-budget checks for 144
parameter combinations, node-resolution checks, the repaired decimal regression,
and actual vacuum requested-width execution. Positive-N numerical evidence comes
from the separately emitted finite stages, not from running these enormous
scheduled matrices. No polynomial precision cost, practical general atom solver,
formal implementation theorem, or novelty claim is made here.

The remaining whole-atom task is to compose this box procedure with the prior
gap-free localization recursion, preserving its error allocation and actual
spectral-infimum target even without binding. That wrapper still needs explicit
code, replayable recursion certificates, and its own review.
