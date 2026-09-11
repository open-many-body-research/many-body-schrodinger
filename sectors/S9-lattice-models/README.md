# S9: Lattice and model Hamiltonians

**Scope.** Hubbard-type models, their exact results, and above all rigorous links between model Hamiltonians and the continuum Coulomb problem.

## Current best (v1.0 foundation)

Nothing worth building on. The exploratory work before publication:
- produced a tautological reformulation of superconductivity in the 2D Hubbard model, and a very weak finite-cluster energy bracket;
- used `native_decide`, which trusts the compiler and so is forbidden here;
- was left out of v1.0.

Known exact results live in the literature, for example Lieb–Wu (1968) and Lieb (1989).

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S9.1 | **Continuum-to-lattice error bound** | For H₂ in a minimal basis, a certified bound on the difference between the two-site Hubbard ground energy and the continuum ground energy | open |
| S9.2 | **Lean: the Lieb (1989) theorems** | Kernel-checked proofs of the ground-state spin of the half-filled bipartite Hubbard model | open |
