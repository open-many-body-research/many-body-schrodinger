> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Complete finite fermionic occupation matrix

This new implementation extends the preceding rank-one stages to the entire
N-electron occupation basis of a finite sine-orbital cube. It implements a
finite-stage continuum enclosure for every finite N,K with `0<=N<=2K^3`, under
the paper continuum and integration lemmas below. It does **not** yet implement
the requested-width general BoxEnclose schedule, prove an optimized bit cost,
or supply a Lean-verified implementation.

Frozen provenance: `TWO_ELECTRON_THEOREM.md`, SHA-256
`7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. General clipping/complement predecessor:
`THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`,
SHA-256 `18093804ba5070c6ad66767432de1ee04eb76bec52bdbe13ee3e0dfc65f4b1bb`.
All prior stages remain unchanged.

## Input, basis and exact convention

The physical inputs are integer N>=0,Z>=1,K>=1, rational R>=1,M>0, positive
integer grid/interval parameters and positive rational eta/eigenvalue tolerance.
The true target is the uncut fermionic Coulomb Dirichlet form infimum on
`Omega_R^N`, `Omega_R=(-2R,2R)^3`; the separate full-space output uses zero
extension and hydrogen lower bounds. N=0 is exactly [0,0]. Spectral/domain
identification is a classical paper dependency, not an assumed Lean theorem.

Enumerate all spatial sine indices in `{1,...,K}^3` lexicographically, with spin
up followed by spin down. The capacity is `L=2K^3`; the full orthonormal N-fold
exterior basis consists of every increasing occupation tuple and has dimension
`m=binomial(L,N)`. No fixed spin sector, spatial symmetry or selected determinant
subset is omitted.

For an increasing tuple S, annihilating occupied index q removes it with sign
`(-1)^(number of members of S below q)`. Creation of an unoccupied p inserts it
with that same preceding-index sign. Occupied creation and unoccupied
annihilation are zero. These are the coordinate identities obtained by moving
the selected factor through the increasing exterior product.

The implementation assembles

`sum_pq h_pq c†_p c_q + (1/2) sum_pqrs g_pqrs c†_p c†_q c_s c_r`,

where

`h_pq=delta_spin(p),spin(q) [delta_spatial(p),spatial(q) t_p - Z nuclear(p,q)]`,

`g_pqrs=delta_spin(p),spin(r) delta_spin(q),spin(s) (pq|rs)`,

and `(pq|rs)=integral phi_p(x)phi_q(y) min(1/|x-y|,M) phi_r(x)phi_s(y) dxdy`.
The rightmost operator acts first: annihilate r, annihilate s, create q, create
p. The factor 1/2 compensates the two ordered particle choices; exchange signs
come from the exterior operations. Interchanging the annihilation order without
changing the coefficient convention would be incorrect.

The kinetic coefficient is `t_p=pi² sum(k_a²)/(32R²)`. All spatial orbitals and
integrals are real, so the full compressed operator has a real symmetric matrix
acting on complex coefficient vectors. This preserves the complex fermionic
space; it does not restrict allowed coefficients to real numbers.

## Integration and Hermitian interval bounds

The implementation uses `general_sine_integrals_v1.py`. Requested grid sizes are
rounded up to the next multiple of every orbital index, and the effective sizes
are explicitly recorded. Every nodal plane then lies on a cell boundary.
Nuclear products and four-index pair products have known cell signs. Positive
and negative difference masses are kept separate through all three coordinate
products and through multiplication by the potential bounds. This is essential
for cross and exchange entries.

Reflection parity cancels exact-zero integrals. For nonzero pair integrals,
commuting the two real factors at x, commuting those at y, and exchanging x,y
permit a canonical cache key. The same exact integral is used at every symmetry
related index tuple; no numerical symmetry assumption about unrelated entries
is made. The clipped representative has value M at collision distance zero,
which is continuous and immaterial on the null collision sets.

Every determinant matrix entry is accumulated with exact rational interval
arithmetic. Both separately assembled intervals for H_ij and H_ji enclose the
same exact entry by Hermitian symmetry. Their intersection is taken, with an
explicit error if it is empty; the intersection is then rounded outward to a
dyadic interval. Thus the returned interval matrix is exactly symmetric and
encloses the true entire compressed matrix.

Its rational midpoint matrix A has perturbation bound
`e=max_i sum_j radius(H_ij interval)`. The sealed exact-rational PSD bisection
produces `[l,h]` for its least eigenvalue, hence `[l-e,h+e]` for the continuum
compression. A variational upper bound also comes from every interval diagonal.

## Full omitted space and both clipping signs

Let P be the whole stated occupation space and Q its orthogonal complement in
the complete fermionic sine-spin basis. P commutes with the kinetic operator.
Every omitted determinant contains at least one spatial orbital with a
coordinate index>=K+1, whose index-square sum is at least `(K+1)^2+2`. Each other
particle has index-square sum at least three. Consequently

`QTQ >= Lambda Q`,

`Lambda=pi_lo²*((K+1)^2+2+3(N-1))/(32R²)`.

This is a conservative lower bound; Pauli exclusions can only increase the
energies of the other particles. It accounts for all states outside the orbital
cube and assumes neither nondegeneracy nor a physical ground-state gap.

With `B=M(NZ+N(N-1)/2)`, bounded Coulomb multiplication and Young's inequality
give `lambda_M>=min(lambda_P_lower-eta,Lambda-B-B²/eta)`. The independent lower
`-NZ²/2` applies to clipped and uncut forms.

For each included determinant i with kinetic energy T_i, pair-only restoration
has expectation at most `(N-1)T_i/M`; nuclear restoration is nonpositive. Thus
`matrix_ii_upper+(N-1)T_i_upper/M` bounds both clipped and uncut minima above.
Dropping nuclear attraction and using the general Hardy pair estimate also
gives the common upper `2T_i_upper+N(N-1)^2/2`. The code takes U to be the minimum
of all these explicit trial bounds.

Both forms satisfy `q,q_M>=T/2-NZ²`; their normalized minimizing-state kinetic
energies are therefore <=`K0=2(U+NZ²)`. With
`delta=(2Z+N-1)/M`, the form bound `|q-q_M|<=delta T` and opposite-minimizer
evaluation imply `|lambda-lambda_M|<=delta K0`. Thus the reported box interval
is

`[max(-NZ²/2,clipped_lower-delta K0), min(U,clipped_upper+delta K0)]`.

The full-space interval uses lower `-NZ²/2` and upper `min(0,box_upper)`.
Bounded-domain minimizers can alternatively be replaced by minimizing sequences
throughout the restoration argument. No full-space attainment is assumed.

## Exhaustive algebra checks

`permutation_determinant_audit_v1.py` independently expands both normalized
Slater determinants as N! signed products. It integrates the one- and two-body
operators by direct spectator Kronecker deltas and divides by N!. It does not
call creation/annihilation functions or a Slater-Condon sign formula.

All 765 matrix entries agree exactly for two rational coefficient families:
an abstract symmetric interaction and a spin-conserving spatial interaction.
The check covers every occupation pair in every N=0,...,4 sector at capacity
four, plus every N=2,3 pair at capacity six. It also checks Hermitian symmetry
and spin-projection selection. The independent exact reference remains finite
test evidence, not a proof of the general implementation.

The separate implementation tests exhaust all 64 Fock states at capacity six
and all 36 pairs of indices for canonical anticommutation identities. A complete
120-by-120 N=2,K=2 constant-clipped-potential matrix encloses the exact diagonal
kinetic energies minus 3M and has offdiagonal intervals containing zero.

## Costs and unresolved requested-width contract

The assembler enumerates m occupations, O(mNL) one-body actions, and
O(mN²L²) two-body actions. It stores m² interval entries. The number of spatial
integrals is bounded by K^6 for nuclear pairs and K^12 for four-index Coulomb
entries, reduced by exact symmetry caches; each finite integral costs O(J³)
interval updates after O(J²) signed convolution work. These are counts to be
combined with operand sizes, not a unit-cost bit-complexity theorem. The
generated rational matrix is dyadic and the finite PSD bit-cost discussion in
`BOX_SOLVER_v1.md` applies with common-rescaled operand lengths.

A general requested-width solver still must choose M,K,entry error/grid/bits
and eigenvalue tolerance together, prove the complete realized budget, and
connect the stage to the recursive full-space localization routine. The present
code accepts finite stage parameters and reports its achieved interval. Passing
a few stages does not prove convergence, practical arbitrary-precision
computation, original Theorem T, or polynomial precision cost.

Commands:

```sh
python3 -B test_occupation_box_stage_v1.py
python3 -B occupation_box_stage_v1.py run --N 2 --K 2 --M 8 --J-nuclear 16 --J-pair 8 --output new_stage.json
python3 -B occupation_box_stage_v1.py check --certificate new_stage.json
```

The checker regenerates every matrix entry and scalar bound and verifies source
hashes. It shares the published arithmetic implementation. Detailed runs and
isolated source replay are recorded separately, without kernel-verification
claims.
