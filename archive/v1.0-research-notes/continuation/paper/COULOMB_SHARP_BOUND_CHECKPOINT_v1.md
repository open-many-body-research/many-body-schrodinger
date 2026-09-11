> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Formal nuclear lower bound for every finite electron count

For every finite \(N\), every real \(Z\), and every actual weak-H¹ full-spin input, the formalized Coulomb form satisfies
\[
q_{N,Z}[\Psi]\ \ge\ -\frac{N Z_+^2}{2}\|\Psi\|^2,\qquad
Z_+=\max\{Z,0\}.
\]
The same lower bound holds for the original weak-H² Hamiltonian graph and for both normalized extended-real energy infima. It includes \(N=0\), \(Z=0\), and negative charges. Fermionic restriction is the original simultaneous spatial/spin antisymmetry; the proof works even before that restriction.

The proof starts from the completed-square inequality in three dimensions,
\[
2t\int\frac{|u|^2}{|x|}
\le \int|\nabla u|^2+t^2\int|u|^2,\qquad t\ge0.
\]
The formal chain uses a regularized radial vector field, genuine compact smooth integration by parts, a complex-valued extension, explicit configuration-space slicing, and the proved smooth compact approximation of actual weak-H¹ derivative witnesses. It therefore does not assume weak slicing, a Sobolev core, the hydrogen spectrum, or any eigenfunction.

For each electron \(i\), the resulting actual configuration-space theorem gives
\[
2t\int\frac{|f|^2}{|x_i|}
\le \sum_{k=1}^{3}\|D_{(i,k)}f\|^2+t^2\|f\|^2.
\]
Set \(t=Z_+\) and sum over electrons. The derivative sums partition the full \(3N\)-coordinate gradient exactly; there are precisely \(N\) mass terms. The physical potential satisfies pointwise
\[
V_{N,Z}(x)\ge -Z_+\sum_i|x_i|^{-1},
\]
because electron repulsion is nonnegative and \(Z_+\ge Z\). Nuclear and full-potential energy integrability are proved before applying integral monotonicity. Combining these inequalities gives the stated bound. Finite-spin summation uses the L² sum-of-squares norm and introduces no \(2^N\) factor. Actual weak integration by parts identifies the form with the original graph's \(-\frac12\Delta+V\).

The coefficient is sharp for the one-body nuclear completed-square inequality. This checkpoint does **not** claim that \(-NZ_+^2/2\) is the optimal many-electron fermionic lower energy. No binding, attainment, gap or ground-state uniqueness is inferred.

The final assembly is [CoulombSharpSemibounded_v1.lean](../lean/CoulombSharpSemibounded_v1.lean), SHA-256 286273e12266d498e154a0b14307499a032970fa5dde9021e83b5049d06c3083. The exact actual weak nuclear theorem is [HydrogenWeak_v1.lean](../lean/HydrogenWeak_v1.lean), SHA-256 a78c848abcd3423734eeb43e2a93357a0701683b077f3e7c38045850c361d34d. The physical expectation comparison is [CoulombAttractiveExpectation_v1.lean](../lean/CoulombAttractiveExpectation_v1.lean).

[COULOMB_SHARP_BOUND_BUILD_PROVENANCE_v1.json](COULOMB_SHARP_BOUND_BUILD_PROVENANCE_v1.json) binds eleven successful source/build records and the independent semantic review. [CoulombSharpSemiboundedAudit_v1.lean](../lean/CoulombSharpSemiboundedAudit_v1.lean) displays the actual weak tests, physical potential, and normalized lower bounds. All audited axiom groups contain only propext, Classical.choice and Quot.sound. Statement expansion has no omissions; proof bodies are intentionally suppressed only in the audit display. Local builds reused pinned dependency objects. The final isolated source rebuild has been requested, not asserted by this checkpoint.

This proof makes no novelty claim. Spectral consequences use the parent program's separately verified self-adjointness and energy-identification modules. Full Theorem T and its quantitative analytic and algorithmic premises remain separate.

Historical preservation provenance is commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660 and tag theorem-t-proof-freeze-2026-09-09. The unchanged original continuum-definition file is AUDIT_2026-09-09_v1/lean/ContinuumFoundation_v1.lean, SHA-256 4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e. All files in this checkpoint are new continuation artifacts.
