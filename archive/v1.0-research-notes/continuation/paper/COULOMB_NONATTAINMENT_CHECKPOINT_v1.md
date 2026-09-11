> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# A continuum spectral bottom with no minimizing vector

For every finite \(N\) and real \(Z\le0\), the actual continuum Coulomb Hamiltonian has zero in its spectrum, its spectrum is real and nonnegative, and the actual H¹ form and original H² graph variational infima both equal zero. If \(N>0\), neither normalized H¹ form inputs nor normalized H² graph inputs attain that infimum. The zero-output Hamiltonian graph has only the zero input.

These are compiled mathematical theorems on the unchanged simultaneous spatial/spin fermionic model. They exhibit a precise parameter class where the requested energy exists as a spectral bottom without a ground-state vector. They make no inference about binding for positive nuclear charge.

The proof separates two facts. For \(Z\le0\), the physical potential is nonnegative. Every nonzero actual weak-H¹ input has positive total gradient energy: if the gradient energy vanished, the proved Hardy norm bound would force its nuclear quotient \(f/|x_i|\) to vanish in L²; nuclear collision nullity then forces \(f=0\). A supplied electron index exists only when \(N>0\), which explains the essential exception.

Thus every nonzero admissible state has strictly positive energy. Nevertheless, the separately verified dilation theorem supplies energy values tending to zero: kinetic energy scales as \(R^{-2}\), Coulomb energy as \(R^{-1}\), after cancellation of the common \(R^{3N}\) mass factor. This proves an infimum of zero. The actual self-adjoint spectral-bottom and nonreal-resolvent theorems identify zero as a spectral point and exclude negative or nonreal spectral points.

Strict positivity for each nonzero state does not imply a positive uniform lower bound. No spectral gap, eigenvalue isolation, full spectral-type classification, or executable eigenfunction computation is asserted.

The sources are [CoulombNonattainment_v1.lean](../lean/CoulombNonattainment_v1.lean), SHA-256 474f56808a02a6fab7fd7b52a6d49a068ce9cb19b2521bf6448722ce200fb3e5, and [CoulombUnboundNonpositive_v1.lean](../lean/CoulombUnboundNonpositive_v1.lean), SHA-256 e62f3a252811903c239e8eeed66bad3f19503b21028a51e5e3fd11eb7dae715f. The final [statement audit](../lean/CoulombUnboundNonpositiveAudit_v1.lean) compiles all assertions together with explicit \(N>0\) and \(Z\le0\).

[COULOMB_NONATTAINMENT_BUILD_PROVENANCE_v1.json](COULOMB_NONATTAINMENT_BUILD_PROVENANCE_v1.json) binds exact successful sources/builds and the [independent review](../audits/coulomb_nonattainment_review_v1.json). Audited theorem dependencies contain only propext, Classical.choice and Quot.sound. There are no statement printer omissions; proof bodies are intentionally suppressed in the semantic audit display. Local builds reused pinned dependency objects. A final isolated source rebuild containing these modules has been requested and is not claimed by this checkpoint.

An initial composition build failed because the parent's final aggregate module was not yet available in the shared build directory. The successful version directly imports the already proved self-adjoint spectral-bottom and nonreal-resolvent modules. It does not assume the missing aggregate theorem or duplicate its energy definition.

Additional H¹ form structure is now verified in [CoulombH1Quadratic_v1.lean](../lean/CoulombH1Quadratic_v1.lean): complex homogeneity, closure under addition/subtraction, and the parallelogram identity. The [quadratic provenance record](COULOMB_H1_QUADRATIC_BUILD_PROVENANCE_v1.json) distinguishes these identities from the separately developing closed-form infrastructure.

No novelty is claimed. Full Theorem T, quantitative physical analytic hypotheses, and complete certified computation remain separate research obligations. All work is in new continuation files; frozen provenance is commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660 and tag theorem-t-proof-freeze-2026-09-09.
