> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# N=3 finite Slater computation with signed exchange

This new stage implements actual Coulomb exchange for a three-electron
fermionic trial. It is distinct from frozen Theorem T and from a complete
arbitrary-precision N=3 algorithm. Evidence is paper-supported exact rational
execution, with classical continuum foundations and an inspectable shared
Python arithmetic implementation; no Lean verification or novelty is claimed.

Frozen provenance: `TWO_ELECTRON_THEOREM.md`, SHA-256
`7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. Predecessor general continuum bounds:
`THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/arbitrary_n/GAP_FREE_COMPUTABILITY_v1.md`,
SHA-256 `18093804ba5070c6ad66767432de1ee04eb76bec52bdbe13ee3e0dfc65f4b1bb`.

## Actual model and Slater state

Inputs are N=3, integer Z>=1, rational R>=1,M>0, finite grid sizes and interval
precision. The target is the true uncut Coulomb Dirichlet form infimum in the
full antisymmetric spin-space on `Omega_R^3`, `Omega_R=(-2R,2R)^3`. The full-space
spectral infimum is separately enclosed by form zero extension. Operator domain
and spectral identification remain paper dependencies rather than implicit
Lean facts. No assertion of full-space binding, uniqueness or spin of the
physical ground state is used.

The normalized Slater state occupies spatial sine orbitals
`phi111 up`, `phi111 down`, `phi211 up`. Its three spin orbitals are orthonormal;
the normalized wedge is antisymmetric under simultaneous spatial/spin
permutation. Standard determinant expansion, spin orthogonality and particle
integration give the clipped energy exactly as

`T-Z(2 nu1+nu2)+J11+2J12-K12`,

where `T=12pi²/(32R²)`, nu1/nu2 are clipped nuclear inverse-radius expectations,
J11/J12 are the direct pair integrals for densities phi111² with phi111²/phi211²,
and K12 is the exchange integral for the two *same-spin* orbitals phi111,phi211.
The opposite-spin pairs have zero exchange because their spin scalar products
vanish. There is exactly one K12 subtraction, not two.

All clipped inverse radii take the value M at zero, a continuous representative
whose values on the null collision sets do not change any integral.

## Direct integrals and the sign-sensitive exchange construction

The direct/nuclear integrals use the exact sine-cell probability primitives
and relative-cell grouping proved in `TWO_ELECTRON_STAGE_v1.md`. For J12 the
one-dimensional x probabilities differ: `s_d=sum_j w1_j w2_(j-d)`. Both sine-square
density arrays obey `wa_(J-1-j)=wa_j`, so reflecting both cell labels proves
`s_-d=s_d`. Swapping unequal densities alone would not prove that symmetry.

The exchange x factor is `sin(pi*t)sin(2pi*t)` with the same normalized
one-dimensional product convention as the overlap primitive. Its sign is
positive for t in (0,1/2), negative in (1/2,1). An **even** J resolves the node
as a grid boundary. Therefore each individual x-cell overlap has a known
mathematical sign independently of its computed interval.

For each absolute label difference d, split products of these signed overlap
cell masses into nonnegative groups P_d (same signs) and N_d (opposite signs,
stored as magnitudes). The y/z factors are ordinary nonnegative phi1² difference
weights. On a grouped relative cell with differences (d_x,d_y,d_z), form the
same exact potential bounds from

`h² sum max(d_a-1,0)² <= |x-y|² <= h² sum(d_a+1)²`, `h=4R/J`.

Multiply that potential interval by the positive group and by the negative
magnitude group separately, then subtract their accumulated integrals. Reflect
signed differences with the exact multiplicity `2^(number of nonzero d_a)`.
This is valid because every original six-dimensional cell product has constant
exchange-integrand sign, and each grouped part is a sum of contributions with
the same sign.

**A naive signed convolution would be invalid:** replacing a collection of
positive and negative masses by their signed sum before applying the potential
range can cancel the very mass that controls variation inside the group. The
implementation deliberately retains both sign groups. It never assumes K12>=0
for the clipped potential. A positive pointwise interaction kernel need not
define a positive convolution operator. The final sum of pair expectations is
nonnegative because it comes from multiplication by the positive pair
potential on the full determinant density; intersecting only that total with
[0,infinity) is valid.

At fixed grids this method costs O(J²) for signed/direct convolutions and
O(J³) interval updates, with actual integer/rational operand costs in addition.
This is a finite-stage statement for these separable orbitals, not an
arbitrary-N or full-solver polynomial cost theorem.

## Degenerate kinetic complement and restoration

The one-electron Dirichlet kinetic levels begin with `3pi²/(32R²)` (two spin
states) and `6pi²/(32R²)` (three spatial orbitals, each with two spins). Thus the
noninteracting three-fermion minimum is `12pi²/(32R²)` and its eigenspace has
dimension six. The selected determinant is one member. Its rank-one P commutes
with the kinetic operator, but Q still contains other minimizing determinants.
Accordingly the code uses only

`QTQ >= Lambda Q`, `Lambda=12pi_lo²/(32R²)`.

It does not import a nondegenerate next-level threshold from N=2. With
`B=M(3Z+3)` and eta>0, the standard P/Q estimate gives
`lambda_M>=min(lambda_P_lower-eta,Lambda-B-B²/eta)`. The clipped upper comes from
the displayed determinant; the elementary full hydrogen lower is `-3Z²/2`.

The absolute clipping form error is `|q-q_M|<=delta T`,
`delta=(2Z+2)/M`. The pair-only restoration error for this trial is at most
`2T/M`; nuclear restoration is nonpositive. Therefore
`U_trial=lambda_P_upper+2T_upper/M` is a common upper bound for both minima.
Independently, dropping attraction and using the general pair bound gives
`q(trial),q_M(trial)<=2T+6<14`, so `U=min(14,U_trial)` is common.

Both forms satisfy `q,q_M>=T/2-3Z²`, hence both minimizing-state kinetic
energies are at most `K0=2(U+3Z²)`. Opposite minimizing-state evaluation gives
`|lambda-lambda_M|<=delta K0`. For a clipped enclosure [a,b], the true box output
is

`[max(-3Z²/2,a-delta K0), min(U,b+delta K0)]`.

The full-space output is `[-3Z²/2,min(0,box_upper)]`. Every change in signs,
particle factors, degeneracy and spin from the preceding N=2 code is explicit.

## Commands and remaining boundary

```sh
python3 -B test_lithium_stage_v1.py
python3 -B exact_lithium_stage_v1.py run --output new_lithium_certificate.json
python3 -B exact_lithium_stage_v1.py check --certificate new_lithium_certificate.json
```

The checker recomputes all integrals and scalar bounds and matches all three
source hashes. It shares the published numerical kernel. Actual results,
independent direct-six-dimensional tests, and source-only replay are recorded
separately. The fixed rank-one trial does not supply a convergent arbitrary-
precision spectral scheme, physical ground-vector accuracy, or a formalized
three-electron theorem. Those are still open.
