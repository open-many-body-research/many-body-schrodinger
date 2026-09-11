> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exact cutoff geometry for either selected electron, N=2

The new result extends the previous selected-index-zero geometry to every i:Fin2, including i=1. It uses an explicit coordinate bijection, not a dimension or cardinality coercion. A spectator coordinate (j,k), where j≠i, maps to k:Fin3; the inverse maps k to (i.rev,k). Fin2 case proofs establish both inverse laws.

The induced spectator linear isometry and its product with the identity in y give physicalSpectatorReindexAt i. This map is a smooth linear isometry and homeomorphism for the actual product norm, with exact forward/inverse basis maps. At i=0 it equals the sealed previous physicalSpectatorReindex, and its spectator factor equals pairCenterEquiv. The previous proof bytes remain unchanged.

For each i, cutoff composition preserves smoothness, compact support and the exact preimage topological support. First and ordered second derivatives map both directions correctly. Explicit finite-sum reindexing proves pointwise equality of combinedCutoffScalar, cutoffGradientWeight and grushinCutoffWeight. The y-radius and the numerical coefficients are unchanged.

SpectatorStepGeometry.pullback_physicalSpectatorReindexAt transports every open region, support and plateau condition with the same M,A,B,D,Q. The final physical_h12_spectatorStepGeometryAt supplies the actual preimages of the existing outer, one-gap and two-gap boxes, using the existing cutoffs and exactly M=D=1, A=h12CutoffScalarBound and B=Q=h12CutoffWeightBound. The c≥0, positive gap, width/radius and actual smooth-transition derivative hypotheses remain explicit.

Three new modules contain 28 declarations: 20 map declarations and eight cutoff/geometry results. Both strict expanded-statement audits compile with complete reports, no printer ellipses and only propext, Classical.choice and Quot.sound. The companion checkpoint binds sources, objects, development and strict receipts, and focused review. Pinned dependency objects were reused; no isolated rebuild was performed.

This closes the selected-electron-one coordinate/geometry omission. It does not assert physical coefficient-patch inclusion of the boxes, transport the weak equation or any integral, prove the finite H12 iteration, or establish an analytic/approximation rate. Those remain separate composition obligations; the physical weak PDE remains on its original actual domain.

Frozen provenance: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09; historical rwa_proof/UNIFORM_ANALYTIC_AUDIT.md SHA-256 5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c. All frozen and prior PASS/sealed bytes are preserved.
