> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exact physical spectator cutoff geometry, version 1

The new Lean result transports the scheduled Fin3 cutoffs into the exact physical spectator index κ=SpectatorCoordinate (0:Fin2). This version covers selected electron zero; it does not yet assert the corresponding result for selected electron one.

The map e=id_Y × pairCenterEquiv is an actual real linear isometry and homeomorphism from Space κ to Space (Fin3), for their ordinary product max norms. Its Y coordinates are unchanged. It maps each actual spectator direction tDir j to tDir(pairSpectatorCoordinateEquiv j), and the inverse maps the basis back. The finite coordinate equivalence and cardinality three are proved, rather than inferred from dimension alone.

For every smooth real cutoff χ, composition χ∘e has exactly the preimage of the old topological support, and compactness and smoothness are preserved. The first and ordered second Frechet derivatives apply the corresponding mapped directions. Consequently the actual expressions combinedCutoffScalar, cutoffGradientWeight and grushinCutoffWeight satisfy exact pullback equalities, for every real c. No norm-equivalence loss or added numerical factor occurs.

The theorem SpectatorStepGeometry.pullback_physicalSpectatorReindex carries Ω,O,W to their exact preimages and χ,η to their compositions, preserving M,A,B,D,Q. Its hypotheses and conclusions are geometric and pointwise cutoff data only; no weak equation or regularity is assumed through the geometry predicate.

The existing H12 cutoff data are assembled into SpectatorStepGeometry on the outer box (ry,rt), intermediate box (ry−δ,rt−δ), and inner box (ry−2δ,rt−2δ), then transported to physical preimages. The actual cutoffs retain the half-gap transition. The constants are exactly M=D=1, A=h12CutoffScalarBound c S C1 C2 δ and B=Q=h12CutoffWeightBound c S C1 δ. Inputs remain c≥0, δ>0, 2δ≤ry,rt, S≥‖a_y‖+2ry, and the actual global first/second smoothTransition derivative bounds C1,C2. This does not supply numerical values for C1,C2 or a positive-c regularity conclusion.

Four new modules, 22 declarations, are bound by the companion checkpoint to development builds, two strict v5 expanded-statement/axiom audits and focused review. Standard foundational axioms only; existing pinned dependency objects reused; no isolated rebuild. Previous PASS, sealed and frozen artifacts remain unchanged.

This unit transports cutoff geometry only. The physical PDE stays in its original domain. Box inclusion in the physical coefficient patch, uniform coefficient/source budgets, the finite analytic iteration, and selected-electron-one transport are separate obligations. The next exact extension uses the projection SpectatorCoordinate i→Fin3 for arbitrary i:Fin2, with inverse selecting its unique other electron.

Frozen provenance: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09; historical rwa_proof/UNIFORM_ANALYTIC_AUDIT.md SHA-256 5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c. No original claim is changed by this coordinate transport.
