> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual weak Coulomb cusp transformation

Evidence: compiled Lean theorems with expanded-statement and transitive axiom audits. This is a Sobolev and PDE result; full Theorem T remains unverified.

For finite electron count \(N\), real charge \(Z\), and the unchanged configuration space \(\mathbb R^{3N}\), set

\[
V=-Z\sum_i |x_i|^{-1}+\sum_{i<j}|x_i-x_j|^{-1},\qquad
F=-Z\sum_i|x_i|+\tfrac12\sum_{i<j}|x_i-x_j|.
\]

The source definitions use totalized reciprocals on collision sets and prove their measure-zero equivalence to the physical potential. The weak derivative identities are on the entire configuration space, including all intersecting collision strata.

**Theorem.** Every real smooth compactly supported \(\chi\) multiplies every actual weak \(H^2\) input \(f\) by \(\chi e^{-F}\) to produce another actual weak \(H^2\) element. The first and all ordered second derivatives satisfy the full weak Leibniz formulas. No eigenfunction or boundedness assumption is required.

The proof constructs \(F_\delta\) by replacing each distance \(r\) with \(\sqrt{r^2+\delta}\). It proves the uniform error

\[
|F_\delta-F|\le\bigl(|Z|N+\tfrac12\tbinom N2\bigr)\sqrt\delta.
\]

First derivatives are uniformly bounded. Mixed second derivatives of \(\chi e^{-F_\delta}\) are bounded by a constant plus a finite sum of inverse nuclear and pair distances. The previously formalized configuration-space Hardy inequalities put this bound times every weak \(H^1\) input in \(L^2\). Dominated convergence supplies strong \(L^2\) limits for every product-jet coordinate; closure of the actual weak derivative relations proves the theorem.

**Eigenfunction consequence.** Suppose the actual scalar graph of \(-\tfrac12\Delta+V\) sends \(f\) to \(E f\), with real \(E\). For \(g=\chi e^{-F}f\), its constructed weak jet satisfies

\[
\Delta g=-2\nabla F\cdot\nabla g-(|\nabla F|^2+2E)g
 +e^{-F}\bigl((\Delta\chi)f+2\nabla\chi\cdot\nabla f\bigr).
\]

The cancellation uses the independently formalized full-space identity \(\Delta F=2V\) and the exact trace of the constructed Hessian. On every ball, a cutoff equal to one gives the homogeneous transformed equation for an actual local representative of \(e^{-F}f\). Explicit finite bounds on every drift coordinate and on the zero-order coefficient depend only on \(N,Z,E\). Neither binding nor a spectral gap is assumed. Applying the scalar result to spin components does not assert existence or uniqueness of an eigenfunction.

The active frontier is the Newton-kernel representation, convolution integrability gain, and a locally Lipschitz representative. Those conclusions are not yet formal consequences of this checkpoint. No approximation rate, certified energy interval, or executable solver is supplied by this result.

## Evidence and reproducibility

- `LOCALIZED_CUSP_H2_MULTIPLIER_CHECKPOINT_v1.json`: 14 sources, 32 strict declarations.
- `COULOMB_TRANSFORMED_EQUATION_CHECKPOINT_v1.json`: 6 further sources, 15 strict declarations, including the next radial-power helper.
- Final physical sources: `../lean/LocalizedCuspWeakJet_v1.lean`, `../lean/CoulombTransformedEquation_v1.lean`, and `../lean/CoulombInteriorTransformedEquation_v1.lean`.
- Lean 4.34.0-rc2, compiler commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`; Mathlib `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`.
- Only `propext`, `Classical.choice`, and `Quot.sound` occur in the audited dependency closures. Classical selection is used for Sobolev witnesses; it is not an executable numerical procedure.
- These development builds reuse pinned dependency and preceding continuation objects. The new sources are outside the 392-source Colab rebuild snapshot. Its final result remains unobserved while browser access is locked. No new isolated-source-reproducibility claim is made.

The preserved historical baseline is commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`, frozen relative path `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`. Its `rwa_proof/RWA_THEOREM.md` has SHA-256 `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`. These bytes remain unchanged.

## Primary-source comparison

The cusp transformation is established mathematics, not a novelty claim. Fournais, Hoffmann-Ostenhof, Hoffmann-Ostenhof, and Sørensen derive the exponential transformation in equation (1.5), give the nuclear/pair factor, and obtain stronger classical regularity using elliptic theory. Their kinetic normalization is \(-\Delta\), requiring coefficient conversion before comparison with the present \(-\tfrac12\Delta\) model. Our factor is fixed by the independently proved \(\Delta F=2V\); their stronger regularity is not imported into Lean. [Author preprint, pages 2–6](https://arxiv.org/pdf/math-ph/0312060).

A recent Ming–Yu preprint reports Barron regularity after cutoff Jastrow factors. Only its abstract has been inspected here; its estimates and applicability to the unchanged trial dictionary remain unreviewed and it is not a proof dependency. [Author preprint abstract](https://arxiv.org/abs/2608.22252). No exhaustive novelty search or independent agent review is claimed.
