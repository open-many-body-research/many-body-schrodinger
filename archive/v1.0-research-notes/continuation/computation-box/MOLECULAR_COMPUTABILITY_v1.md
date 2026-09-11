> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Rational fixed-nucleus molecular electronic and total energies

Evidence: a paper-supported implemented algorithm, exact finite arithmetic
tests and certificate replay. The continuum foundations and Python runtime
are not Lean verified. This is a separate extension of the v2 gap-free atomic
algorithm, with no assertion about the frozen Theorem T dictionary or RATE.

## Finite physical input and exact output

The input is N>=0, p>=1 integers and a nonempty finite list of distinct centers
a_l in Q^3 with charges z_l in Q_{>0}. JSON coordinates and charges are integers
or rational strings; floating-point and Boolean nuclear values are rejected.
Coincident centers are rejected, making the nucleus-nucleus constant finite.
The number of nuclei, all signed integer numerators and positive denominators,
N and p form the finite binary input. Centers are canonicalized by exact
lexicographic order. No arbitrary external potential or unspecified oracle is
part of the input.

The electronic operator is

    H_el = -1/2 sum_i Delta_i
           - sum_i sum_l z_l/|x_i-a_l|
           + sum_(i<j) 1/|x_i-x_j|.

Its Hilbert space is the full fermionic subspace of
L2(R^(3N); C^(2^N)), with simultaneous permutation of electron coordinates
and spin labels. Its operator domain is the actual weak H2 space intersected
with that fermionic subspace. The spectral infimum E_el, including cases where
it is not attained, is the target. No molecular rotation symmetry, unique
wavefunction, binding, excited-state gap or ground-state attainment is used.

`electronic_enclose` returns a rational interval of width <=2^-p containing
E_el. `born_oppenheimer_enclose` returns a rational interval of width <=2^-p
containing the clamped-nucleus energy E_el+C_nn, where

    C_nn = sum_(l<m) z_l z_m / |a_l-a_m|.

The electronic and nuclear-repulsion certificates remain separately visible.
There is no optimization over nuclear positions and no nuclear kinetic term.
The output is an energy interval, not a wavefunction or observable guarantee.

The box routine uses the corresponding Dirichlet form on (-2R,2R)^(3N), R>=1,
intersected with the full fermionic spin space. The finite basis is exactly
all N-particle occupations of both spins of the K^3 normalized cube sine
orbitals. Its dimension is binom(2K^3,N). Trial functions extend by zero as
H1 functions for variational upper bounds; no H2 zero-extension assertion
is required. The operator H2 statement concerns the full-space realization.

## Translated continuum bounds

Let S=sum_l z_l and Q=ceil(S)>=1. Q is only a conservative bound used in error
constants. The actual implemented potential still uses each exact z_l and
a_l; replacing S by Q does not replace the physical Hamiltonian.

Translation preserves collision-set nullity and the three-dimensional Hardy
bound. Applying the existing sliced/spin-summed proof separately to each
electron/nucleus pair gives infinitesimal Laplacian relative boundedness.
There are finitely many nuclei and pairs. The same Kato-Rellich and closed
form argument as in the atomic branch therefore gives self-adjointness on
H2, fermionic restriction, semiboundedness, and equality of the variational
and spectral infima. The translated/sliced realization and form proof for this
molecular representation remain paper mathematics, despite the separate atomic
operator and exact-H2 formalization progress. A matrix certificate does not
establish these molecular analytic steps by itself.

One can check the useful constants without assuming coincident nuclei.
For one electron, write its kinetic energy T_i and decompose

    T_i - sum_l z_l/|x_i-a_l|
      = sum_l (z_l/Q)(T_i-Q/|x_i-a_l|) + (1-S/Q)T_i.

Each translated hydrogen term is bounded below by -Q^2/2. The coefficients
are nonnegative with sum<=1, so the expression is >=-SQ/2>=-Q^2/2.
The same argument applied with half the kinetic energy gives
T_i/2-sum_l z_l/|x_i-a_l| >=-SQ>=-Q^2. Adding the nonnegative pair potential
yields, for both the true and clipped forms,

    q >= -NQ^2/2,                 q >= T/2-NQ^2.

For clipped forms, nuclear attraction is weaker and clipped pair repulsion
is still nonnegative, so these lower bounds still hold.

Clip every inverse distance to min(1/r,M), taking value M at r=0; the collision
representative differs only on a null set. The elementary inequality
(1/r-M)_+ <= 1/(4Mr^2), translated Hardy, and the existing relative-coordinate
pair Hardy bound give

    |q-q_M| <= [(2Q+N-1)/M] T.

The separate sign information matters. Unclipping attraction lowers a fixed
trial energy; unclipping pair repulsion raises it by at most (N-1)T/M. Thus
both forms share the upper bound obtained by taking the minimum of

    diagonal(q_M) + (N-1)T_trial/M,
    2T_trial + N(N-1)^2/2.

For either normalized minimizer, or a minimizing sequence with vanishing
energy slack, q>=T/2-NQ^2 then gives T<=2(U+NQ^2) in the limit. Evaluating
the restoration inequality on **each appropriate minimizing state** bounds
the two differences of infima. This does not incorrectly infer a two-sided
energy difference from evaluating only the clipped minimizer.

The potential norm bound B=M[NQ+N(N-1)/2], complete-basis kinetic complement
pi^2[(K+1)^2+2+3(N-1)]/(32R^2), and Schur/Cauchy lower bound from
`OCCUPATION_MATRIX_STAGE_v1.md` are unchanged. In particular no artificial
spectral gap is introduced by the molecular extension.

## Actual translated integral and finite matrix

`translated_nuclear` integrates each signed sine-product cell over the **full
cube**. It subtracts the rational center a_l from each coordinate interval
before computing exact minimum and maximum squared distances. Inverting
the directed square-root enclosure bounds the clipped potential throughout
that cell. Each one-dimensional product has a constant known sign because
its grid resolves the scalar orbital nodes. The product sign is applied
only after multiplying nonnegative mass intervals and the positive potential
interval. Thus no cancellation of signed uncertainty is used as a bound.

Origin reflection and orbital-parity cancellation are not applied to an
off-center nucleus. In particular a translated (111,211) nuclear matrix
entry need not vanish. Full-cube integration also may produce a wider
interval at an origin-parity zero than the specialized atomic kernel; this
is a difference in sharpness, not a change of the underlying matrix.
The tests check containment of the sharper atomic intervals in that case.

The nuclear cache key contains the unordered orbital pair and the exact
nucleus index. Each pair of orbitals gets a local resolving grid below
J0+K^6, and each pair Coulomb integral one below J0+K^12. The translation
does not move orbital nodes. Pair integrals, exact spin Kronecker factors,
creation/annihilation signs, all occupation states, Hermitian interval
intersection, midpoint row-error bound and rational PSD bisection reuse
the already reviewed implementation. Nuclear integrals are multiplied by
the exact rational charge before assembly.

## Requested width and full-space localization

The box scalar plan is the v2 atomic plan with bounding charge Q. The explicit
anchor U0 does not depend on nucleus positions because all attractive terms
can be dropped in an upper estimate. All clipping, complement and rounding
budgets therefore apply. Summing the translated nuclear Lipschitz constants
gives S M^2<=Q M^2. The same D=4RM^2[NQ+2N(N-1)] and J0 prescription bound
each row's spatial uncertainty. The v2 arithmetic endpoint-excess bound also
applies: translation changes exact rational distance inputs, while using
the full cube has multiplicity one instead of the prior bound eight.
The absolute sum of nuclear charge coefficients is S<=Q. Thus the explicit
sufficient b from `precision_cost_bound_v2.py` with Q still proves finite
termination of the actual bit-doubling acceptance loop.

For localization let

    A = max_l (|a_l,1|+|a_l,2|+|a_l,3|).

This rational number bounds every Euclidean nuclear radius. In an IMS sector
with at least one electron outside the radius-R inner region, R>A implies
each outside electron sees nuclear attraction no worse than -Q/(R-A).
Repulsive cross terms may be dropped. The same subgroup-antisymmetric slicing
as in the atomic argument bounds retained electrons by the corresponding
smaller-electron molecular energy. Adding electrons at arbitrarily distant
positions with vanishing kinetic energy gives E_k<=E_(k-1), without assuming
attainment of either infimum. Therefore the unchanged IMS construction gives

    E_k >= min(E_box,k, E_(k-1)-kQ/(R-A)) - 5k/(4R^2),
    E_k <= min(E_box,k, E_(k-1)).

For a requested N,p the code iterates k=1,...,N with

    p_k=p+3(N-k),  epsilon_k=2^(-p_k-3),
    R_k=k(2Q+1)/epsilon_k + 2A.

Then R_k>=2A, kQ/(R_k-A)<=epsilon_k and 5k/(4R_k^2)<=epsilon_k.
The previous interval has width<=epsilon_k by the precision shift, and the
box interval has width<=epsilon_k. Taking minima of their endpoints and
subtracting the two scalar error terms gives width<=3epsilon_k<2^-p_k.
The code checks these exact rational width comparisons. The vacuum electronic
energy is [0,0]. No electron-binding premise is introduced by this recursion.

For C_nn, each distinct rational center pair has positive squared distance.
Successive dyadic square-root refinements eventually give a positive lower
endpoint and a contracting reciprocal interval. The implementation rounds
the **final sum** outward before testing its requested width. It evaluates
the electronic energy at p+1 and the constant at width2^(-p-1), so their sum
has width<=2^-p. This separate constant changes neither the electronic
domain nor any electronic eigenvector.

## Cost and trust boundary

For fixed N and a fixed finite rational molecular input, A,Q and the number
of nuclei are constants; R_k remains O(2^p). The v2 bounds for M,K,m,J*, b
and PSD bisections therefore give the same 2^O(p) deterministic bit-cost
upper bound in the stated schoolbook integer model. The hidden constants
now depend explicitly on the finite nuclear input as well as N.
There is no claim of uniform polynomial cost as nuclei or electron counts
grow, or polynomial dependence on p.

For variable molecular input, every coordinate and charge numerator and
denominator contributes its actual binary length. The translated squared
distance arithmetic has operand size polynomial in these lengths and
log J,log R. At most L_nuc K^6 nuclear cache entries are evaluated. Charge
weighted sums have common denominator dividing the product of the supplied
charge denominators times the dyadic denominator, so its bit length is at
most the sum of those input lengths plus the dyadic precision; repeated
matrix accumulation does not multiply new unrelated denominators.
Final matrix rounding restores the dyadic common denominator used by the
reviewed PSD minor/Hadamard argument. Nuclear-repulsion reciprocal costs
also depend on the represented minimum nuclear separation; it is positive
and effectively bounded below by the maximum nonzero coordinate difference
for each pair. These dependencies cannot be silently dropped from a claim
about growing molecular size.

Correct certificates require the actual continuum/form results, translated
integration proof and exact runtime arithmetic. Fresh replay uses the same
Python arithmetic implementation; finite tests and an independent review
do not turn this into a kernel-verified implementation. No positive-N full
conservative requested-width schedule or spectral eigenvector is asserted
to have been computed. Actual finite-stage molecule outputs and replay
results are recorded separately in the execution record.

## Preservation

This is new work under `CONTINUATION_2026-09-09_v2/computation/box/`.
Its immediate predecessor seal is `LOCAL_GRID_SEALED_MANIFEST_v2.json`,
SHA-256 `6896cf3520fa75304f1fd4c772bcad4442ea7e697f473c9d47a6bc0521d40dfd`.
Frozen source provenance remains commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`; frozen
`THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md` has SHA-256
`7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`.
All earlier sources, certificates, corrections and reviews remain unchanged.
