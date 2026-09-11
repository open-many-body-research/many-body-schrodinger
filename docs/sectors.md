# Sectors and open problems

The problem is split into nine sectors, so that people can work in parallel without stepping on each other. Each problem has:

- an ID (`S3.2`),
- a **checkable deliverable** at a stated evidence tier, and
- the **current best** result in this repository.

To start on one, open a *Claim a problem* issue (see [CONTRIBUTING.md](../CONTRIBUTING.md) §8).

Status legend: **open** (nobody has claimed it), **claimed** (see the linked issue), **improved** (a better result has been merged, but the stated target hasn't been reached yet), **done**.

| Sector | Scope | v1.0 foundation holdings |
|---|---|---|
| [S1](../sectors/S1-foundations/README.md) | Operator theory: self-adjointness, domains, spectrum, HVZ, bound states | Lean: self-adjointness and ground-energy bounds for *atoms* (one nucleus, all N, real Z) |
| [S2](../sectors/S2-two-electron-theory/README.md) | Two-electron theory: ground-state existence, separators, "Theorem T" (a certified, polynomial-bit-cost algorithm for two-electron atoms) | Lean: helium ground branch and gap. Paper level: analytic chain. **Theorem T is open.** |
| [S3](../sectors/S3-certified-computation/README.md) | Certified energy intervals for concrete systems (He, H⁻, H₂, …) | Exact-arithmetic helium certificates. The H₂ result is effectively trivial. |
| [S4](../sectors/S4-three-electrons/README.md) | Lithium and other N = 3 systems | Trivial bounds only |
| [S5](../sectors/S5-arbitrary-N/README.md) | Algorithms for arbitrary N: computability, cost, box localization | Paper-level computability with exponential cost; not executed at useful widths |
| [S6](../sectors/S6-molecules/README.md) | Molecules and multi-center problems; efficient general methods | Open |
| [S7](../sectors/S7-complexity/README.md) | Complexity and hardness | Literature summary; continuum hardness open |
| [S8](../sectors/S8-regularity-approximation/README.md) | Regularity of eigenfunctions and approximation rates | Paper-level claims that need human review (triple-collision analyticity, dictionary rates, fixed-exponent obstruction) |
| [S9](../sectors/S9-lattice-models/README.md) | Lattice and model Hamiltonians and their relation to the continuum | Textbook-level results only |

## Most wanted

These are the problems where a result would help the most people:

1. **S3.1: a non-trivial certified H₂ lower bound.** Nobody in the repository has one yet, and it needs a better separator (S3.2) plus cusp-capable trial functions (S3.3).
2. **S8.1: human review of the triple-collision analyticity claim.** If it's correct, it's the most significant mathematical claim in the foundation. If it's wrong, the S2 program needs a new route.
3. **S1.2: extend the Lean foundations from atoms to molecules** (M fixed nuclei).
4. **S2.3: connect the helium certificate to the Lean theorem**, so that a Lean statement `E_He ∈ [ℓ, u]` is kernel-checked end to end.
5. **S4.1: any certified lithium enclosure narrower than 10⁻² Ha.**
