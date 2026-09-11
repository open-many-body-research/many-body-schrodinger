# S7: Complexity

**Scope.** How hard is it, in the worst case, to compute ground energies to a given precision? This covers hardness, whether fixed-$N$ cases are tractable, and how finite-basis results relate to the continuum.

## Known (literature, not claims of this repository)
- **Local Hamiltonians.** The 2-local Hamiltonian problem is QMA-complete (Kempe–Kitaev–Regev 2006).
- **Density-functional theory.** Computing the universal functional of DFT is QMA-hard (Schuch–Verstraete 2009). Their construction needs engineered external fields.
- **Fixed-basis electronic structure.** Electronic structure in a fixed finite basis is QMA-hard (O'Gorman–Irani–Whitfield–Fefferman 2022).
- **Consequence.** A polynomial-time classical solver for these finite-basis instances at inverse-polynomial precision would imply P = QMA.

## Current best (v1.0 foundation)

| Claim | Result | Tier |
|---|---|---|
| S7-001 | QMA-hardness for bound point-nucleus molecules in the continuum | O |
| S7-002 | "Sharp no-go" for gap-limited transfer | X (tautology) |

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S7.1 | **Continuum hardness** | A polynomial-time reduction from 2-local Hamiltonians to non-magnetic point-nucleus Coulomb molecules, with inverse-polynomial gap and ionization margin, or a structural obstruction to one | open |
| S7.2 | **Fixed-$N$ complexity** | For fixed $N$, place certified $p$-bit ground-energy computation in a complexity class (e.g. polynomial in $p$). Theorem T is the case $N=2$. | open |
