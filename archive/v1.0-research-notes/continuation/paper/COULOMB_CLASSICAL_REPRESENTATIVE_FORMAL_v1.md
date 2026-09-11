> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual Coulomb eigenfunctions: weak orders, smooth representatives and the pointwise equation

Evidence category: fully formalized mathematical regularity results, with compiled final statements and complete expanded-statement and axiom audits. This is not an executable energy approximation procedure.

## Exact result

Let N be a finite positive integer, Z and E real, and f an actual complex L2 equivalence class on R^(3N) satisfying the existing scalar Hamiltonian graph equation H f = E f. The graph uses actual weak H2 derivatives and

H = -(1/2) sum_i Delta_i - Z sum_i |x_i|^(-1) + sum_(i<j) |x_i-x_j|^(-1).

There is a representative g of f which is locally Lipschitz on the entire configuration space. At every configuration with x_i != 0 and x_i != x_j for i != j, g is C-infinity and satisfies, pointwise,

Delta g(x) = 2 (V_(N,Z)(x) - E) g(x).

The derivatives in this equation are the actual Frechet partial derivatives in the original Euclidean coordinate basis. The representative is the same everywhere, including the collision configurations where the result only asserts locally Lipschitz regularity. No smoothness, weak derivative hierarchy, or pointwise PDE assumption is added to the Hamiltonian graph premise.

For the actual full fermionic spin space, the result holds simultaneously for every spin component of every eigenvector. The representatives satisfy pointwise antisymmetry under simultaneous permutation of spatial coordinates and spin labels. The previously established square-sum amplitude bound M_(N,Z,E) ||psi|| is retained without an extra factor for the number of spin configurations. The inherited finite M contains an unevaluated Sobolev coefficient; it is not claimed to be a computed numerical constant.

This regularity theorem is conditional on a genuine eigen-equation, as a regularity theorem should be. It does not assert that every permitted atom has an eigenvector at its spectral infimum. The previously established two-electron existence theorem is separate.

## Proof chain

1. Actual finite weak order is defined recursively using L2 weak derivative witnesses. Order one and order two are proved equivalent to the original H1 and H2 predicates. For actual L2 elements f and h, the distributional equation Delta f = h and weak order n of h imply weak order n+2 of f. This uses the proved Fourier/Bessel Laplacian gain and commutation of actual distributional derivatives.

2. Smooth compact multiplication preserves every finite order. Nested cutoffs prove that a weak derivative loses precisely one available local order, without assuming equality of arbitrary representatives on slices. The unsoftened Coulomb coefficient is smooth off the exact collision set. Localizing the actual eigen-equation therefore gains one order at a time. Every cutoff supported in that open set has every finite weak order; one cutoff equal to one near a specified point provides one L2 representative with all orders simultaneously.

3. Weak order 2m gives Bessel Sobolev order 2m. The weighted Fourier representation is identified with the actual pointwise product of the L2 Fourier representative; product membership is concluded, not assumed. Cauchy-Schwarz with a proved integrable inverse Bessel weight gives integrability of every Fourier moment. The calculation is dimension dependent and does not claim dimension independent constants.

4. Lp functions defining the same tempered distribution are equal almost everywhere. Fubini identifies the Fourier integral of an L1 function with its distributional transform, and this identifies the actual L1 and L2 transforms. For a continuous integrable representative with all weak orders, the proved Fourier moment criterion and Fourier inversion yield actual C-infinity regularity. Applying this to a compact cutoff times the already proved locally Lipschitz physical representative establishes smoothness near every collision-free point.

5. Weak derivative uniqueness identifies every supplied weak first and second derivative of a compact smooth representative with its classical derivatives almost everywhere. The exact cutoff Laplacian identity and the actual eigen-equation give the classical PDE almost everywhere on a ball where the cutoff equals one. Continuity on that open ball upgrades equality to every point. Equality of the localized and original functions near the center identifies their actual second derivatives there.

The same scalar argument applies to each actual spin component. Pointwise antisymmetry comes from the previously proved continuous representative theorem; it is not imposed on independently selected point values.

## Evidence and limitations

The companion checkpoint `../audits/COULOMB_CLASSICAL_REPRESENTATIVE_CHECKPOINT_v1.json` identifies the final source hashes and strict receipts. Only propext, Classical.choice and Quot.sound occur in their axiom dependencies. Source statements and definitions were inspected as well as axiom reports. There are no admitted mathematical obligations in this chain. Auxiliary cutoff and quotient selections are noncomputable mathematical constructions.

Development uses Lean 4.34.0-rc2 and pinned Mathlib d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9, reusing pinned dependency objects and successful continuation objects. These sources are outside the 392-module Colab rebuild snapshot. The final state of that rebuild is unobserved. Earlier completed source-rebuild checkpoints cover their stated earlier scopes only. No independent agent review of this new chain was possible because agent usage was exhausted.

Classical Coulomb regularity is not claimed as new. The earlier primary-source comparison includes Fournais, M. Hoffmann-Ostenhof, T. Hoffmann-Ostenhof and Sorensen, *Sharp regularity results for many-electron wave functions*, [arXiv:math-ph/0312060](https://arxiv.org/abs/math-ph/0312060). No theorem from that paper is imported as an axiom. This checkpoint claims the formal results above, not the stronger sharp regularity claims of that paper.

No real analyticity, factorial derivative bound, scale uniform constant, physical weak KS equation, dictionary approximation rate, or full Theorem T follows from C-infinity regularity alone. Those obligations remain active. The next step is the actual KS differential identity retaining all spectator directions, followed by a weak equation on coefficient patches and a justified extension through the selected collision.

## Frozen provenance

Historical starting point: `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Frozen sources and earlier successful continuation sources are unchanged. The actual all-local-weak-orders checkpoint precedes this one.
