> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Formal two-electron ground branch

This result concerns the actual continuum Coulomb Hamiltonian
\(H_{2,Z}=-\tfrac12(\Delta_1+\Delta_2)-Z/r_1-Z/r_2+1/r_{12}\)
on the full spin-space with simultaneous spatial and spin antisymmetry.
Its operator domain is the actual weak H² space intersected with that fermionic
space. The established shared foundation identifies its variational infimum
with the bottom of its actual spectrum.

For every real \(Z>0\) satisfying \(32<9Z^2\), that bottom \(E_Z\) is an
eigenvalue, with a unit H² eigenvector, and
\[
 E_Z<-5Z^2/8,\qquad
 \sigma(H_{2,Z})\subset\{E_Z\}\cup[-5Z^2/8,\infty).
\]
The eigenspace at \(E_Z\) is a complex line. Normalized vectors are unique up to
unit complex phase. Every eigenvector below the separator has singlet spin.
There is a real almost everywhere, exchange-symmetric, unit spatial H²
eigenfunction at \(E_Z\). No positivity or pointwise regularity follows merely
from this H² statement.

For every real \(Z\ge2\), the explicit conservative estimates are
\[
 E_Z\le-9Z^2/14,\qquad
 \sigma(H_{2,Z})\setminus\{E_Z\}\subset[E_Z+Z^2/56,\infty).
\]
Thus helium has a proved complement separator of \(-5/2\), with a spectral gap
lower bound \(1/14\) hartree.

The proof combines the actual one-electron hydrogen rank-one H¹ comparison
with configuration-space slicing and the fermionic joint product projection.
It gives, with the actual unit hydrogen product singlet \(G_Z\),
\[
 q_{2,Z}(\psi)\ge -5Z^2\|\psi\|^2/8
                    -3Z^2|\langle G_Z,\psi\rangle|^2/8.
\]
The unit trial \(G_Z\) belongs to the intended H² domain. Its exact energy is
\(-Z^2+R_Z\), where \(R_Z\) is its actual repulsion expectation. A proved
relative-coordinate Coulomb uncertainty inequality and the exact hydrogen
gradient norm give \(R_Z\ge0\) and \(R_Z^2\le Z^2/2\). These bounds imply the
strict trial inequality in the stated charge range. The finite-rank comparison,
self-adjointness and spectral-bottom machinery then establish attainment,
the complement bound and spectral exclusion. The rational relaxation
\(R_Z\le5Z/7\) yields the uniform gap above. Conjugation of the actual weak
graph yields a real eigenfunction.

For all \(Z>0\), if an actual unit H² vector has mean
\(L\le\mu\le U<-5Z^2/8\) and centered continuum residual squared at most \(r\),
then its certified spectral enclosure is
\[
 L-\frac{r}{-5Z^2/8-U}\le E_Z\le U.
\]
The comparison is proved; the vector and directed mean/residual bounds remain
inputs to this implication. An executable producer is a separate obligation.

Exact source hashes and expanded-statement/axiom receipts are in
`audits/PHYSICAL_GROUND_BRANCH_CHECKPOINT_v1.json` and
`audits/PHYSICAL_GROUND_STRUCTURE_CHECKPOINT_v1.json`.
Lean 4.34.0-rc2 and pinned Mathlib are used. Only `propext`, `Classical.choice`
and `Quot.sound` occur in these axiom audits. Development builds reuse pinned
dependency objects. The running Colab source rebuild covers the earlier
392-target snapshot; the later spin, realness and uniform-gap modules are
explicitly outside that snapshot.

The exact repulsion moment \(5Z/8\) was not assumed by these formal proofs.
Its formalization and the better optimized charge range remain separate.
The original dictionary, rate, solver, termination and bit-complexity claims
of full Theorem T remain unverified. Rotation invariance, physical decay and
the analytic approximation chain remain active obligations. These results
make no claim of novelty of the underlying physical theorem.

Frozen reference: `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`,
tag `theorem-t-proof-freeze-2026-09-09`. Frozen artifacts are unchanged.
