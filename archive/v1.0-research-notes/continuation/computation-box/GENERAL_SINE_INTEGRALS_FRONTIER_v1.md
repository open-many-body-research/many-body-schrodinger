> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# General matrix-entry primitive: current frontier

`general_sine_integrals_v1.py` is a new finite procedure for nuclear cross
integrals and four-index clipped Coulomb integrals of arbitrary three-index
Dirichlet sine orbitals. The mathematical normalization and rational interval
kernel are the same as the sealed N1/N2/N3 stages. Three grouped tests pass,
including exact equality with earlier direct/exchange stage outputs and
constant-kernel orthogonality for higher/crossed orbitals. This version has not
yet received independent general-case review or been linked to an arbitrary-N
algorithm; it must not be reported as a completed general BoxEnclose.

For positive integer orbital indices a,b,c,d and rational R,M>0, the pair target
is `integral phi_a(x)phi_b(y) min(1/|x-y|,M) phi_c(x)phi_d(y) dxdy`. Nuclear
targets are the corresponding two-index inverse-radius integrals. All outputs
are rational intervals. `resolving_grid` uses an integer least common multiple
to make J divisible by every orbital index. This places every nodal plane on a
grid boundary. The sign of each sine in each open cell is determined exactly
from the rational midpoint phase; a computed floating sign is never used.

Nuclear odd coordinate parity gives exact zero. Coulomb odd *total* parity of
the four indices in any coordinate gives exact zero under simultaneous
reflection of that coordinate of x and y. In the even case reflection preserves
the sign of every complete cell-pair integrand, so positive and negative
difference groups are separately equal at d and -d. For each axis, P_d,N_d
store nonnegative magnitudes grouped by sign. Combining axes uses
`(P,N)*(A,B)=(PA+NB,PB+NA)`. The potential interval is applied to the resulting
positive and negative groups separately. This preserves the mass needed to
control within-cell potential variation; signed cancellation happens only
after both integrals have been enclosed.

Each finite call uses O(J²) one-dimensional convolution updates and O(J³)
three-dimensional difference updates, with the actual rational bit cost in
addition. It caches sine/overlap values through the sealed primitive library.
This is not an assertion that outputting a full many-electron matrix is cheap.
Choosing J along multiples of the fixed indices and then increasing interval
precision gives convergent entry bounds by continuity of the clipped potential,
constant cell signs, integrability and normalized Cauchy–Schwarz bounds.
An explicit allocation linking that convergence to the prior matrix-error
budget remains to be implemented and independently checked.

The next executable work is a full fermionic finite matrix assembler:

1. Enumerate spin orbitals `(k1,k2,k3,spin)` and N-element occupation sets.
2. Use the exact exterior-algebra creation/annihilation signs to assemble one-
   and two-body matrix elements, including spin Kronecker factors.
3. Produce a symmetric rational midpoint matrix with entry intervals and row
   perturbation bound; apply the sealed exact PSD bisection.
4. Connect that matrix to the full kinetic complement, two-sided clipping
   restoration, and the requested-width parameter schedule.
5. Test small cases against the sealed stages and independently derive all
   spin/normalization/sign conventions before claiming a general contract.

The required second-quantized interaction convention must be fixed explicitly,
for example `1/2 sum_pqrs (pq|rs) c_p† c_q† c_s c_r` with
`(pq|rs)=integral phi_p(x)phi_q(y) v(x-y) phi_r(x)phi_s(y)` and matching spin
delta factors. Confusing the annihilation order changes exchange signs.

This file identifies an active code frontier, not a new theorem status. The
frozen baseline and original two-electron dictionary remain unchanged; their
provenance is recorded in `BOX_SOLVER_v1.md` and the sealed stage manifests.
