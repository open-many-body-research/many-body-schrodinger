> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Rung 2 status

Several major proof stages remain. This is not final assembly, and neither a completion percentage nor a delivery date is supported by the evidence.

| Stage | Current boundary |
|---|---|
| Actual continuum operator and physical two-electron ground state | Formal foundations and ground-state structure established. |
| Regularity needed by the approximation | Physical H12 initialization, coherent all-order weak derivatives, full compact weak weighted estimate and common coefficient factorial bounds established. The actual solution factorial bound is still being composed. |
| KS descent and global H2 approximation in the original dictionary | Paper arguments reviewed; complete formal chain remains open. |
| Certified rational algorithm | Full implementation correctness, emitted-interval proof and termination remain open. |
| Complexity and final Theorem T | Operational bit-cost analysis and final composition remain open. Original2256 and1/16 are not verified. |

Immediate next milestone: derive the quantitative recurrence for actual local derivative norms and prove its pointwise/Taylor consequence. The scalar recurrence solution is already formally proved, conditional on that PDE recurrence.

New proofs use the pinned Lean/Mathlib development cache. They are outside the last isolated source rebuild. Evidence and exact boundaries: [root checkpoint](R02_GRAPH_TO_FACTORIAL_ROOT_CHECKPOINT_v1.json).
