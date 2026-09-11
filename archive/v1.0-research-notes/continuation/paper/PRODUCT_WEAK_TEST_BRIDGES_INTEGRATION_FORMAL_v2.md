> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Product weak-test bridges, compatible integration version

For arbitrary finite-dimensional real inner-product spaces `Y,T`, actual complex
L² inputs `f,g` on the ordinary Cartesian product, and every product direction
`v`, the following are equivalent:

\[
\int\varphi g=-\int(D_v\varphi)f
\quad\text{for every real }\varphi\in C_c^\infty(Y\times T),
\]

and the actual tempered-distribution identity

\[
\partial_{\operatorname{toLp}_2(v)}\operatorname{lift}(f)
=\operatorname{lift}(g).
\]

Here the lift is the existing L² linear isometry onto the Euclidean `WithLp 2`
copy, preserving product Lebesgue measure exactly. The original Cartesian
product keeps its maximum norm. `WeakProductL2Directional` is defined by the
displayed compact-test identity using actual Fréchet derivatives; its
equivalence to the tempered identity has no additional hypothesis.

The exact final theorem is `weakProductL2Directional_iff_distribution` in
`lean/ProductDistributionDirectionalConverse_v2.lean`. Its forward direction
uses canonical exact weak-jet lift transport and the proved generic
compact-test-to-Schwartz converse. Its reverse direction uses the existing
tempered-to-compact-test theorem, followed by exact unlift transport and the
proved identity `productEuclideanUnlift_lift` for both L² inputs.

The companion `ProductCompactTestTransport_v2` and
`ProductCompactLaplacianConverse_v2` preserve the mathematical statements of
the previous compact factor-Laplacian result: if actual product L² inputs
`f,w` satisfy `∫ φ w = ∫ (L_{Y,T} φ) f` against every real smooth compact test,
where `L_{Y,T}` is the sum of actual second derivatives in two orthonormal
factor bases, then the Euclidean-copy tempered Laplacian equals the lift of
`w`, and `f` has actual weak first and all ordered second L² derivatives.

The integration correction resolves duplicate global declaration names from
independent proof branches. `ProductCompactTestTransport_v1` and
`ProductWeakDirectionalLift_v1` each defined `productEuclideanLift_test`.
The separately compiling `ProductDistributionDirectionalConverse_v1` also
defined `weakL2Directional_productEuclideanLift`, which is already present in
`ProductWeakDirectionalLift_v1`. These definitions caused the branches to be
incompatible for a combined import. This is an integration issue; the
individual compiled proofs do not establish a false mathematical statement.

The canonical shared owner is now the unchanged, previously verified
`ProductWeakDirectionalLift_v1`. `ProductCompactTestTransport_v2` imports that
owner and omits its duplicate pairing declaration. The version 2 Laplacian
converse imports this new transport. The version 2 directional converse imports
the canonical owner and reuses its weak-jet lift theorem. All successful
version 1 bytes remain preserved. For future combined development, import
the version 2 converse modules together with the unchanged
`ProductCompactH2Approximation_v1`; the superseded version 1 converse branch
is a separate historical environment and should not be co-imported.

The joint strict audit deliberately imports all three version 2 modules and
`ProductCompactH2Approximation_v1` in one environment. It checks expanded
statements and complete axiom reports, in addition to verifying that the two
proof branches compose. Only `propext`, `Classical.choice`, and `Quot.sound`
are admitted. Source/object hashes and the exact audit receipt are recorded in
`audits/PRODUCT_WEAK_TEST_BRIDGES_INTEGRATION_CHECKPOINT_v2.json`.

Development checks use Lean 4.34.0-rc2 and reuse pinned library, prior-audit,
and continuation objects. These sources are outside the sealed 671-target
desktop rebuild snapshot. There is no new local Grushin regularity theorem,
quantitative local estimate, computable derivative selection, analytic
regularity result, or full Theorem T claim here. No novelty claim is made.

Preservation anchor: frozen `rwa_proof/RWA_THEOREM.md`, SHA-256
`d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`.
