> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# The exact finite-electron Coulomb graph on the weak H² fermionic domain

Evidence: compiled Lean theorem with expanded statements and transitive axiom audit.
This is a shared continuum foundation, not self-adjointness, a spectral theorem,
a ground-state uniqueness theorem, full Theorem T, or a new efficient solver.
No literature novelty is claimed.

## Statement

For every finite electron count N≥0 and every real Z, let X_N=R^(3N) with its
actual Lebesgue measure, and let Sigma_N={up,down}^N. The Hilbert space is the
finite Hilbert sum of L²(X_N;C) over all spin labels. Its fermionic subspace
imposes the sign of every simultaneous permutation of coordinates and spin
labels. Let D_N consist of its elements whose every spin component has every
first and every ordered second distributional derivative in L². This is the
original weak Sobolev H² domain intersected with the fermionic space.

The potential is the actual Coulomb function

V_(N,Z)(x) = −Z sum_i |x_i|^(-1) + sum_(i<j) |x_i−x_j|^(-1).

Inverse zero is assigned Lean's value zero only as a representative convention.
The nuclear and pair collision sets have been proved Lebesgue null, including
the finite union, so this convention does not change the physical L² objects.

**Theorem.** A spinor ψ has exactly one output h in the original weak Coulomb
graph if and only if ψ belongs to D_N. The output is fermionic and satisfies,
componentwise almost everywhere,

h = −(1/2) sum_k ∂_k² ψ + V_(N,Z) ψ.

The existing linear partial operator defined by this concrete graph therefore
has domain exactly D_N. Its domain is dense in the genuine fermionic Hilbert
space. These statements require no extra Coulomb-product, graph-totality,
output-symmetry, eigenfunction, binding or spectral hypothesis.

## What supplies the missing multiplication step

The new proof first establishes the real and complex three-dimensional
compact C¹ Hardy inequality, including actual integrability of the singular
square and actual L² membership of the inverse-distance product. A regularized
vector-field identity gives the constant4; Fatou passes to the singular limit.

An exact linear-isometric configuration split and product-volume identity lift
the estimate by Tonelli. A translated three-dimensional slice treats pairs.
Global singular integrability is proved before integrating the sliced bounds.
The compact estimates have the appropriate electron-direction gradients.

Actual weak derivatives commute with smooth convolution, as proved by testing
the original weak derivative against translated kernels. Normalized nonnegative
convolution contracts L² by Jensen and Fubini. Explicit smooth cutoffs with
uniform first-derivative bound C_N/R and a normalized shrinking mollifier sequence
supply the two limiting arguments. This extends each singular estimate to the
actual weak H¹ domain. The initial weak extension uses the full gradient:

integral |f|²/|x_i|² ≤ 4 sum_k ||d_k||²,
integral |f|²/|x_i−x_j|² ≤ 4 sum_k ||d_k||².

Here d_k are genuine weak derivatives, not selected surrogates. Finite sums now
prove V f∈L² for every actual weak H¹ input, hence for every weak H² input.
Sharper directional N-dependent constants and gradient/Laplacian interpolation
remain separate quantitative work; none is assumed to obtain this graph result.

## Assembly and dense definition

The weak derivatives and the potential are proved covariant under the actual
coordinate permutations. Scalar graph uniqueness therefore proves output
fermionic symmetry. The finite spin sum introduces no missing output-symmetry
hypothesis. Graph linearity constructs a linear partial operator; the new
multiplication theorem identifies its domain exactly.

Density uses the concrete finite antisymmetrizer

Aψ = (1/N!) sum_(π in S_N) sgn(π) U_πψ.

It is a continuous projection onto the actual fermionic subspace and preserves
weak H². Applying it to the proved dense smooth compact L² class proves density
of D_N. The proof does not infer density by intersecting an arbitrary dense set
with a closed subspace. Operator-domain density follows only after domain
equality is established. No assertion that functions avoiding collisions form
an H² core is made.

The mathematical operator is noncomputable Lean data obtained from its proved
single-valued graph. This is not an executable Hamiltonian evaluator or an
implementation of the certified energy procedures.

## Exact verification evidence

Final public composition: `lean/CoulombDomainTotal_v2.lean`, SHA-256
`6576473d8d8d1ee59b0fff59e31d35b10f76b03db1da1a627ee6182f0a47d7c6`.
Its five public theorems are:

- hamiltonian_graph_existsUnique_of_targetDomain
- hamiltonian_graph_existsUnique_iff_targetDomain
- coulombPartialOperator_domain_iff_H2
- coulombPartialOperator_domain_eq_H2
- coulombPartialOperator_domain_dense

The decisive scalar multiplication dependency is `lean/WeakCoulombL2_v2.lean`,
SHA-256 `d74b5a3cb1358cd771e2e394baf635310918325a9ee01c982db45e253b681fe7`.
Every output theorem uses only propext, Classical.choice and Quot.sound.
There are no added mathematical axioms, sorry, sorryAx or native_decide trust
mechanisms in the successful dependency audit. Expanded statements expose the
mathematical binders; proof terms and instance bodies are suppressed for reading.

The final composition and weak-transfer/cutoff group audit is
`audits/formal_semantics/20260909T234148_538908Z/receipt.json` (23 declarations).
Its source/object hashes were stable during the audit. The physical slicing and
weak multiplication audit is
`lean/logs/collision_nullity/slice-hardy-expanded-receipt-20260909T233956Z.json`
(34 declarations). Earlier semantic reviews establish the original physical
objects, scalar assembly, permutation conventions and antisymmetrizer.

Environment: Lean4.34.0-rc2, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`; mathlib revision
`d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`.
These successful project-module checks reused pinned dependency object caches.
The isolated source rebuild is a separate ongoing experiment; completion of this
cached audit must not be reported as a completed fresh dependency-source build.
Reproduce the project-module check with

`python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py CoulombDomainTotal_v2`

## Preservation and next theorem

The historical source is `THEOREM_T_FREEZE_2026-09-09_212604/`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag
`theorem-t-proof-freeze-2026-09-09`. Frozen `RWA_REPORT.md` SHA-256 is
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
All original artifacts and prior completed audits remain unchanged.

This corrects the starting boundary by discharging the full-graph/domain
existence frontier. It does not yet complete the specification's quantitative
Fourier-interpolation sub-obligation. The next active analytic/formal obligations
are operator symmetry, actual Laplacian interpolation, a resolvent construction,
self-adjointness, semiboundedness and variational/spectral energy identification.
The original two-electron analytic dictionary theorem remains unverified.
