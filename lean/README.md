# Lean library: v1.0 foundation

- **Toolchain:** `leanprover/lean4:v4.34.0-rc2`.
- **Mathlib:** commit `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`. All dependencies are pinned in `lake-manifest.json`.
- **Scope:** 817 modules, byte-identical to the set that was rebuilt from source during pre-publication work. `SHA256SUMS` lists every file.

```bash
cd lean
lake exe cache get      # Mathlib build cache for the pinned commit
lake build              # builds all 817 modules
cd .. && python3 tools/axiom_audit.py   # #print axioms for every declaration cited by a tier-L claim
```

## Where to start reading
Each item below is a module name; its source is at `Foundation/<name>.lean`.

| Module | What it contains |
|---|---|
| `ContinuumFoundation_v1` | The definitions: configuration space, $L^2$ spaces, the antisymmetric subspace, the Coulomb potential, weak derivatives, $H^1$/$H^2$, the Hamiltonian graph |
| `CoulombOperatorCore_v2` | `coulombPartialOperator`, the Hamiltonian as a Mathlib `LinearPMap` |
| `UnboundedResolvent_v2` | `unboundedSpectrum` (bounded two-sided inverse) |
| `CoulombSpectralFoundation_v3` | S1-001: self-adjointness and ground-energy identification |
| `HydrogenSpinGround_v1`, `HydrogenExactSolver_v1` | S1-003: hydrogen |
| `CoulombRankOneBranch_v1`, `CoulombRankOneCertificate_v1` | S2-001: ground branch and Temple enclosure |
| `TwoElectronPhysicalGroundBranch_v1`, `TwoElectronPhysicalCertificate_v1` | S2-002 and S2-003: two electrons and helium |

The claims these modules support, with exact declaration names, are listed in [`../claims/registry.yaml`](../claims/registry.yaml), and each claim has a statement card in [`../claims/cards/`](../claims/cards/).

## Things to know
- **Flat module names.** Modules are imported by bare name (`import CoulombSpectralFoundation_v3`). The `_vN` suffixes record the history of their development. Several versions of some modules coexist because later modules still import the earlier ones. Compile each module separately (as `lake build` does). Don't write an umbrella file that imports everything: nobody has tested that, and different versions may clash.
- **Namespace.** Declarations live under the `TheoremT.*` namespace. The name refers to the research program's target theorem, which is **not** proved (see [ERRATUM-001](../errata/ERRATUM-001-theorem-t-not-proved.md)). Nothing in this library states or proves Theorem T.
- **Noise.** Many files contain inline `#print axioms` commands, and the build emits linter and deprecation warnings. Neither affects soundness.
- **Checked.** `tools/lean_policy.py` finds no `sorry`, `admit`, axiom declarations, `native_decide`, `implemented_by`, `extern`, `unsafe` or `opaque`. It ignores comments; one docstring mentions the word "axiom".
- **New work.** Put new work in new modules, preferably under a `ManyBody/` directory with proper namespaced module names. Leave the foundation files unchanged. If a foundation file is wrong, write an erratum ([CONTRIBUTING.md](../CONTRIBUTING.md) §2).
