> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual H¹ form and H² operator energy: formal checkpoint

For every finite \(N\) and real \(Z\), the normalized infimum of the actual fermionic weak-H¹ Coulomb quadratic form equals the unchanged original weak-H² Hamiltonian-graph variational infimum:
\[
\inf_{\substack{\Psi\in H^1_{\mathrm{ferm}}\\\|\Psi\|=1}}q_{N,Z}[\Psi]
= E_{\mathrm{var}}(N,Z).
\]
The theorem does not assume attainment, binding, a spectral gap, uniqueness of a ground vector, or \(N>0\). Its left side is defined as an extended-real infimum of genuine form values; it does not assign an arbitrary finite number to an empty trial set.

The physical form is
\[
q_{N,Z}[\Psi]=\frac12\sum_k\|D_k\Psi\|^2+
\sum_{\sigma\in\{0,1\}^N}\int_{\mathbb R^{3N}}
V_{N,Z}(x)|\Psi_\sigma(x)|^2\,dx.
\]
Here the full finite-spin norm is the original sum-of-squares norm; fermionic membership enforces simultaneous spatial and spin permutation. The potential is the original untruncated Coulomb potential. The formalization proves integrability of each potential energy density, existence of the value for every actual weak-H¹ input, and independence from derivative and potential-output witnesses. This is uniqueness of the form value, not uniqueness of a physical state.

The proof of infimum equality has three concrete steps. First, actual weak integration by parts identifies the form value on every H² graph input with the original Rayleigh numerator. Second, the proved Coulomb bound implies \(V\Psi_n\to V\Psi\) in L² whenever every first weak derivative converges in L²; hence form energies converge under H¹ graph convergence. Third, the new actual fermionic H²-in-H¹ density theorem transfers each homogeneous operator lower bound \(a\|\Psi_n\|^2\le q[\Psi_n]\) to the H¹ limit. This avoids normalizing approximants that could initially vanish. The original variational energy's separately proved finiteness permits the final extended-real comparison.

The strongest exact source is [CoulombH1Infimum_v1.lean](../lean/CoulombH1Infimum_v1.lean), SHA-256 f420538e03750817e41308182a830277c5b935f177ad812cbb33222d2230ffe6. It also proves equality of all H¹-form and actual-operator quadratic lower bounds. The literal integral formula appears in [CoulombH1IntegralForm_v1.lean](../lean/CoulombH1IntegralForm_v1.lean). [CoulombH1FormAudit_v1.lean](../lean/CoulombH1FormAudit_v1.lean) expands the physical spaces, compact smooth test equations, simultaneous permutation condition and normalized infima.

The [build provenance](COULOMB_H1_FORM_BUILD_PROVENANCE_v1.json) binds eleven source/build records and the [independent review](../audits/coulomb_h1_form_review_v1.json). All reported axiom groups contain only propext, Classical.choice and Quot.sound. The semantic audit has no statement printer omissions; theorem proof bodies are deliberately suppressed in its display and remain compiled in the source modules. Local builds reused the pinned dependency cache. Inclusion in the final isolated source rebuild is requested, not claimed here.

This package proves form-energy equality. A closed-form representation theorem and identification with the spectrum are separate results; the parent program composes the latter from its actual self-adjoint operator development. Full Theorem T, its analytic approximation chain and its certified precision algorithm remain separate unresolved obligations.

The current next obligation is the sharp elementary lower bound \(-N(\max\{Z,0\})^2/2\), using a proved nuclear uncertainty inequality and nonnegativity of electron repulsion. The present package already includes a correct coarser semibound.

The preserved original continuum-model source is AUDIT_2026-09-09_v1/lean/ContinuumFoundation_v1.lean, SHA-256 4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e. Frozen project provenance: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660 and tag theorem-t-proof-freeze-2026-09-09. All artifacts in this checkpoint are new continuation files.
