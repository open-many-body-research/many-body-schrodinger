# S6: Molecules and efficient general methods

**Scope.** Multi-center Coulomb problems with clamped nuclei: formal foundations, separators, certified bounds, and rigorous guarantees for practical methods (coupled cluster, DMRG, QMC, neural ansätze).

## Current best (v1.0 foundation)

| Claim | Result | Tier |
|---|---|---|
| S6-001 | $`-N(\sum_A Z_A)^2/2 \le E_N \le 0`$ for any geometry | P1 (proved in Lean for atoms: S1-001) |

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S6.1 | **Lean: the molecular operator** (same as S1.2) | Self-adjointness and ground-energy identification for $`M`$ nuclei | open |
| S6.2 | **Uniform molecular separator** | A computable lower bound on the second eigenvalue for H₂ over a range of $`R`$ | open |
| S6.3 | **A posteriori guarantees for a practical method** | For one practical method on one small molecule (e.g. LiH at equilibrium), a certified bound on the method's error with respect to the continuum $`E_0`$ | open |
| S6.4 | **Born–Oppenheimer error** | Explicit, certified bounds on the error of the clamped-nucleus approximation for H₂ | open |
