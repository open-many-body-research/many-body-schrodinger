# Open Many-Body Schrödinger Program

**A verified, shared record of rigorous progress on the electronic many-body Schrödinger equation, set up so that people can split up the problem, work on different pieces, and build on each other's results.**

$$
H_N=\sum_{i=1}^{N}\Big(-\tfrac12\Delta_{i}-\sum_{k}\frac{Z_k}{|x_i-R_k|}\Big)+\sum_{i<j}\frac{1}{|x_i-x_j|}
\quad\text{on antisymmetric } L^2\big((\mathbb R^3\times\{\uparrow,\downarrow\})^N\big)
$$

Physics and chemistry already have excellent *numbers* for small atoms and molecules. What they lack are **verified** results:
- theorems checked by a proof assistant, and
- energy intervals that are *guaranteed* to contain the true answer.

This repository only records results at that standard. Every result carries an **evidence tier**, and only machine-checked Lean proofs (**L**), exact-arithmetic certificates (**C**) and independently reviewed proofs (**P2**) count as established.

> **What this is not.** It is not a solution of the many-body problem, and it does not claim an efficient algorithm. The research program's target theorem ("Theorem T": polynomial-cost certified ground energies for two-electron atoms) is **open**. An earlier internal report claimed it was proved; that claim is withdrawn in [ERRATUM-001](errata/ERRATUM-001-theorem-t-not-proved.md).

---

## v1.0 foundation: what is established

| | Result | Tier |
|---|---|---|
| **Operator theory** | For **every** electron number $N$ and nuclear charge $Z$, the atomic Coulomb Hamiltonian with spin and Fermi statistics is self-adjoint on exactly $H^2$. Its variational, form and spectral ground energies coincide, and the common value $E$ lies in $[-N\max(Z,0)^2/2,\ 0]$. This is Kato's theorem (1951), now **formalized in Lean 4 / Mathlib**. | [L](claims/cards/S1-001.md) |
| **Hydrogen** | The ground energy is exactly $-Z^2/2$, identified inside the unbounded continuum operator. | [L](claims/cards/S1-003.md) |
| **Two electrons** | For $9Z^2>32$ (helium included): the ground state exists and is nondegenerate, $E < -5Z^2/8$, and every other spectral point has real part $\ge -5Z^2/8$. Temple's enclosure is proved for the actual operator. | [L](claims/cards/S2-002.md) |
| **Helium energy** | $E_\text{He}\in[-2.903724385192751581540207,\ -2.903724377006065467379698]$ Ha, width $8.2\times10^{-9}$. Exact rational arithmetic, standard-library Python, reproduced in CI. | [C](claims/cards/S3-002.md)* |

\* The helium certificate relies on the Lean separator and Temple step plus closed-form moment formulas that are proved on paper (tier P1) and spot-checked on more than 3,000 exact identities. See the card.

All results, including the open and withdrawn ones, are listed in **[STATUS.md](STATUS.md)**. It is generated from [`claims/registry.yaml`](claims/registry.yaml).

## Sectors: pick a piece of the problem

| Sector | Scope | Where v1.0 stands |
|---|---|---|
| [S1 Foundations](sectors/S1-foundations/README.md) | Self-adjointness, spectrum, HVZ, bound states | Atoms done in Lean; molecules open |
| [S2 Two-electron theory](sectors/S2-two-electron-theory/README.md) | Separators, ground-state structure, Theorem T | Helium ground branch in Lean; Theorem T open |
| [S3 Certified computation](sectors/S3-certified-computation/README.md) | Guaranteed energy intervals | Helium to 8e-9 Ha; **no non-trivial H₂ lower bound** |
| [S4 Three electrons](sectors/S4-three-electrons/README.md) | Lithium and N = 3 regularity | Essentially unstarted |
| [S5 Arbitrary N](sectors/S5-arbitrary-N/README.md) | Certified algorithms and their cost | Paper-level computability only |
| [S6 Molecules](sectors/S6-molecules/README.md) | Multi-center problems, guarantees for practical methods | Open |
| [S7 Complexity](sectors/S7-complexity/README.md) | Hardness in the continuum, fixed-N complexity | Open |
| [S8 Regularity and approximation](sectors/S8-regularity-approximation/README.md) | Coalescence structure, explicit approximation rates | Paper claims awaiting **human expert review** |
| [S9 Lattice models](sectors/S9-lattice-models/README.md) | Hubbard-type models and their link to the continuum | Open |

The most wanted problems are listed in [docs/sectors.md](docs/sectors.md#most-wanted).

## Verify everything yourself

```bash
# Certificates (Python 3 standard library only)
python3 certificates/run_checks.py --quick     # seconds
python3 certificates/run_checks.py --full      # ~15 min: re-derives all 16 helium certificates

# Lean (Lean 4.34.0-rc2, Mathlib d9ed2b07; installs via elan)
cd lean && lake exe cache get && lake build && cd ..
pip install pyyaml && python3 tools/axiom_audit.py   # only propext, Classical.choice, Quot.sound allowed

# Repository rules
python3 tools/lean_policy.py        # no sorry / axiom / native_decide / ...
python3 tools/validate_registry.py  # tiers, evidence, dependencies
```

CI runs all of these on every pull request ([`.github/workflows/verify.yml`](.github/workflows/verify.yml)).

## Contributing

Anyone can fork this repository and open pull requests. Only maintainers can merge, and nothing merges without passing CI and a code-owner review. The rules, in short (full version in **[CONTRIBUTING.md](CONTRIBUTING.md)**):

1. **Claim a problem.** Open a *Claim a problem* issue for a sector problem so that work isn't duplicated.
2. **Bring evidence that matches your tier:**
   - **L:** Lean with no `sorry`, `axiom`, or `native_decide`, and standard axioms only.
   - **C:** an exact-arithmetic certificate with a separate checker that CI runs.
   - **P2:** a complete proof with two independent reviews.
3. **Write a statement card** saying, in plain language, what the formal statement means, which hypotheses are *assumed*, and what it does **not** show.
4. **Never edit a foundation result in place.** File an erratum instead. Wrong results are downgraded, never deleted.

AI assistance is allowed, and it was used heavily to build v1.0. It must be disclosed, and it never substitutes for kernel checking or human review. See [GOVERNANCE.md](GOVERNANCE.md) for roles, review and dispute rules.

## Repository map

```
claims/        registry.yaml (authoritative status) and statement cards
lean/          Lean 4 library: 817 modules, v1.0 foundation
certificates/  exact-arithmetic helium certificates and checkers
sectors/       one README per sector: current best and open problems
docs/          problem statement, sector map, bibliography
proposals/     paper proofs awaiting review (P1)
reviews/       review records (P1 → P2)
errata/        corrections and withdrawals
archive/       the v1.0 research notes (context, not authority)
tools/         CI checks
```

## Provenance

The v1.0 foundation was produced by an independent researcher working with extensive AI assistance (automated proof search, Lean formalization agents, and AI "reviewers"). Before publication it was audited skeptically:
- results that turned out trivial or overstated were downgraded or withdrawn;
- only the Lean modules whose from-source rebuild is recorded were included;
- every certificate was re-derived.

No human expert has yet reviewed the paper-level claims. That review is the most valuable contribution you can make.

## License and citation

- **Code and Lean sources:** [Apache-2.0](LICENSE).
- **Text and proofs:** [CC BY 4.0](LICENSE-DOCS).
- **Citing a result:** cite the claim ID and the release tag, e.g. "S2-002, Open Many-Body Schrödinger Program v1.0-foundation". See [CITATION.cff](CITATION.cff).
