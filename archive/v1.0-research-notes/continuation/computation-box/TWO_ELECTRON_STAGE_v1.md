> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Two-electron stage with an actually integrated pair interaction

This is a separate finite-stage algorithm, not the frozen Theorem T dictionary,
not its complexity theorem, and not a terminating arbitrary-precision N=2 box
solver. Its purpose is to exercise actual fermionic spin, positive pair
interaction, both Coulomb clipping signs, and a complement lower estimate in
an executed certificate. Evidence: exact rational execution with the following
paper-level continuum link; no Lean verification is claimed.

Frozen provenance: `TWO_ELECTRON_THEOREM.md`, SHA-256
`7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. The predecessor general clipping/complement
proof is `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`,
SHA-256 `18093804ba5070c6ad66767432de1ee04eb76bec52bdbe13ee3e0dfc65f4b1bb`.
No prior source or certificate is modified by this branch.

## Actual state and target

N=2, integer Z>=1, rational R>=1. The target is the bottom Dirichlet form energy
of

`H=-1/2(Delta_x+Delta_y)-Z/|x|-Z/|y|+1/|x-y|`

on `Omega_R^2`, `Omega_R=(-2R,2R)^3`, in full antisymmetric two-electron spin-space.
Its form domain is fermionic `H^1_0(Omega_R^2; C^4)`. Identifying this variational
infimum with the actual self-adjoint spectrum depends on the classical continuum
foundations, which remain unproved in Lean in the parent project.

Let phi be the normalized spatial `(1,1,1)` Dirichlet sine orbital. The normalized
Slater determinant of `phi spin_up` and `phi spin_down` is exactly
`phi(x)phi(y)*(up down-down up)/sqrt(2)`. This is antisymmetric under simultaneous
exchange of spatial and spin labels. Its spin-summed spatial density is
`|phi(x)|^2 |phi(y)|^2`, not twice or half that density. Its kinetic energy is
`T=6pi^2/(32R^2)`.

For K=1 there are exactly two one-electron spin orbitals and their N=2 wedge
space is one-dimensional. Thus the implementation's rank-one P is the complete
specified Galerkin space, including spin, rather than an unannounced spatial
symmetry assumption.

## Clipped integrals and a finite exact grouping

Clip both inverse radii and the pair inverse distance at the same rational M>0.
The resulting scalar compression is

`lambda_P=T-2Z I_nuclear+I_pair`.

The normalized one-dimensional probability in a grid cell j is
`w_j=2 integral_(j/J)^((j+1)/J) sin^2(pi*t) dt`. The existing exact-rational sine
primitive encloses every w_j in a nonnegative interval.

The nuclear expectation uses products of three cell probabilities and the
potential extrema given by exact rational minimum/maximum squared distances
from the origin. Symmetric reflected cells are grouped with integer
multiplicity, including the self-reflecting central cell if J is odd.

For the pair integral, let h=4R/J. Group two one-dimensional cell labels j,k by
d=j-k. The probability of a signed difference d>=0 is

`s_d=sum_(j=d)^(J-1) w_j w_(j-d)`.

For negative d, `s_(-d)=s_d` by exchanging j and k. If d>=0, the difference of
points in those cells lies in `h[d-1,d+1]`. Thus for a vector of absolute cell
label differences `(d_1,d_2,d_3)` the minimum/maximum possible squared distance
are

`r_min^2=h^2 sum_a max(d_a-1,0)^2`,
`r_max^2=h^2 sum_a (d_a+1)^2`.

The clipped inverse-distance on all such six-dimensional cell products lies
between the clipped values at these two extremes, in reverse order. Multiply
this interval by `prod_a s_(d_a)` and multiplicity
`2^(number of nonzero d_a)`, then sum over `{0,...,J-1}^3`.

This exactly groups the six-dimensional Cartesian sum; no independence of
distance and density inside a cell is assumed. A bounded potential interval
times the exact positive cell probability is a valid integral interval for
every such cell. Since the normalized density factorizes in all six individual
coordinates, grouped weights are products of the one-dimensional convolutions.
The two electron coordinates are independent under this trial density, although
their distance is of course coupled by the interaction. All arithmetic error is
included in the outward intervals.

The finite procedure uses O(J²) interval operations for the convolutions and
O(J³) pair-cell updates, with integer/rational operand costs charged separately.
This improvement applies to this particular separable rank-one density; it is
not a complexity bound for arbitrary many-electron determinants or correlated
states. Constant clipping and a brute six-dimensional rational convolution
identity supply independently known tests of the grouping.

## Complement lower bound

The lowest spatial kinetic orbital has energy `3pi²/(32R²)` and two spin copies.
The next spatial level has energy `6pi²/(32R²)`. Fermionic exclusion permits two
electrons in the lowest spatial orbital only with the two opposite spin states,
which is the single determinant already in P. Every omitted determinant has at
least one next-level orbital and one orbital of energy at least the lowest
level. Completeness of the sine-spin wedge basis therefore gives

`QTQ >= [9pi_lo²/(32R²)]Q = Lambda Q`.

Clipped nuclear/pair multiplication has norm at most `B=M(2Z+1)`. The same
orthogonal decomposition and Young inequality used in `BOX_SOLVER_v1.md` give

`lambda_M >= min(lambda_P_lower-eta, Lambda-B-B²/eta)`

for every eta>0. Also `lambda_M<=lambda_P_upper`. Dropping positive pair
repulsion and completing two hydrogen squares yields `q,q_M>=-Z²`; the code
intersects its lower bound with this independently justified estimate.

## Both clipping signs and a useful direct upper bound

Nuclear unclipping lowers energy; pair unclipping raises it. Neither q<=q_M nor
q>=q_M is valid for all states. The prior Hardy/slicing proof gives the absolute
form bound

`|q-q_M| <= delta T`, with `delta=(2Z+1)/M`.

Both forms obey `q,q_M >= T/2-2Z²`. For any common upper bound U on their minima,
both normalized minimizing states have `T<=K0=2(U+2Z²)`. Evaluating each form at
the opposite minimizing state yields

`|lambda-lambda_M| <= delta*K0`.

The code obtains a useful U from its actual trial: the pair-only clipping error
is at most `T_trial/M`, whereas the nuclear correction is nonpositive. Therefore

`q(trial) <= lambda_P_upper+T_trial_upper/M = U_trial`,

and `q_M(trial)<=lambda_P_upper<=U_trial`. Independently, dropping attractions,
Hardy gives pair expectation `<=2sqrt(T)<=T+1`; hence both trial forms are at
most `2T+1<5` for R>=1. Thus `U=min(5,U_trial)` is a common upper bound.

With a clipped enclosure `[a,b]`, return

`[max(-Z²,a-delta*K0), min(U,b+delta*K0)]`.

The full-space energy also lies in `[-Z²,min(0,box_upper)]` by zero extension
of this fermionic Dirichlet trial and the full-space hydrogen lower bound.
This does not require binding, a ground-state vector, uniqueness, or a gap in
full space. At feasible parameters the elementary lower bound may be stronger
than the evaluated complement/restoration formula; the report says so.

## Implementation and checking

`exact_two_electron_stage_v1.py` imports the sealed exact rational primitives
from `exact_box_v1.py` (source SHA-256
`f1358f9f63f025554128a20ad2d464934509a6363ae49bc028cba92e2673ad58`). Each emitted
certificate records hashes of both files. The `check` command recomputes every
integral and every scalar bound and checks both source hashes. It shares the
published implementation and is not a separately verified kernel.

```sh
python3 -B test_two_electron_stage_v1.py
python3 -B exact_two_electron_stage_v1.py run --output new_two_electron_certificate.json
python3 -B exact_two_electron_stage_v1.py check --certificate new_two_electron_certificate.json
```

The source accepts explicit finite grid sizes. It has no arbitrary-precision
N=2 termination theorem because K remains one. This is a real certified-stage
computation under paper foundations, with explicit remaining formal obligations.
It is not full Theorem T, a proof of its exponents, or completion of arbitrary-N
BoxEnclose. See the separate execution receipt for actual rational outputs,
performance, independent review, and isolated source reproduction.
