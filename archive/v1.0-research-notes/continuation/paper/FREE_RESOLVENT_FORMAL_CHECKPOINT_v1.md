> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual free resolvent and Coulomb composition: formal checkpoint

The actual positive free resolvent has been constructed and verified for every finite electron count \(N\), every \(\mu>0\), and every scalar continuum input \(f\in L^2(\mathbb R^{3N};\mathbb C)\). With the pinned library's Fourier convention \(e^{-2\pi i x\cdot\xi}\),
\[
R_\mu=\mathcal F^{-1}(2\pi^2|\xi|^2+\mu)^{-1}\mathcal F,\qquad
K_\mu=\mathcal F^{-1}\frac{2\pi^2|\xi|^2}{2\pi^2|\xi|^2+\mu}\mathcal F.
\]
These are actual complex continuous linear maps on the original continuum L² space, satisfying
\[
\|R_\mu\|\le\mu^{-1},\qquad \|K_\mu\|\le1,\qquad
K_\mu f+\mu R_\mu f=f.
\]
The output \(R_\mu f\) lies in the unchanged weak H² domain: all first and all ordered mixed second derivatives exist in actual L². The theorem supplies these witnesses and proves
\[
f=-\tfrac12\sum_k\partial_k^2(R_\mu f)+\mu R_\mu f.
\]
No domain existence hypothesis or Fourier-domain substitute is assumed. The proof uses the separately verified equivalence between the original weak H² definition and the distributional-Laplacian/weighted-Fourier domain.

The actual untruncated Coulomb multiplication composed with this resolvent is also a continuous linear map. For
\[
C=2\left(|Z|N+\binom N2\right),
\]
the compiled bound is
\[
\|V_{N,Z}R_\mu\|\le\tfrac14+\frac{2C^2}{\mu}.
\]
Thus the concrete shift \(\mu=1+8C^2\) gives norm at most \(1/2\), including \(N=0\) and \(C=0\). This is a scalar prerequisite for the separately developed fermionic lift and Neumann argument. Uniqueness, left inverse, self-adjointness and spectral conclusions are not attributed to this source package alone.

The principal sources are [FreeResolvent_v1.lean](../lean/FreeResolvent_v1.lean), [FreeResolventMultiplier_v1.lean](../lean/FreeResolventMultiplier_v1.lean), and [CoulombResolvent_v1.lean](../lean/CoulombResolvent_v1.lean). Exact hashes, successful build receipts, logs, axiom groups and the independent adversarial review are bound by [FREE_RESOLVENT_BUILD_PROVENANCE_v1.json](FREE_RESOLVENT_BUILD_PROVENANCE_v1.json). The mathematical statement expansion is [FreeResolventSemanticAudit_v2.lean](../lean/FreeResolventSemanticAudit_v2.lean): its literal physical spaces, multiplier and every weak-test clause compile without statement omissions. A previous successful 134 MB implementation-expanded audit is preserved; its remaining printer omissions are disclosed rather than treated as complete expansion.

All audited theorems use only the standard foundational axioms propext, Classical.choice and Quot.sound. The definitions are mathematical continuous linear maps; no executable numerical resolvent or cost bound is claimed. The local builds used pinned dependency objects with Lean v4.34.0-rc2 and mathlib revision d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9. A final isolated source rebuild containing this newer branch has been requested and is not claimed by this checkpoint.

The preserved original continuum model is AUDIT_2026-09-09_v1/lean/ContinuumFoundation_v1.lean, SHA-256 4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e. Historical project provenance is frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. No frozen source bytes were changed.
