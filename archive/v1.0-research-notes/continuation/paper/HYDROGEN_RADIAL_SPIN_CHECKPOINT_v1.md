> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exact one-electron continuum ground energy and spin eigenfamily

The Lean theorem `TheoremT.Continuum.hydrogen_full_spin_ground` now proves, for
every real charge `Z > 0`, that the original weak-H² variational energy, the
physical H¹ form energy, and the bottom of the actual continuum spectrum all
equal `−Z²/2` for `N = 1`. The Hamiltonian is the unchanged
`−(1/2)Δ − Z/|x|` on the actual weak Sobolev H² domain, with the full two-label
spin space and simultaneous spatial/spin permutation rule.

The eigenvectors are explicit. For `c : Fin 2 → ℂ`, the spin component at
`σ : Fin 1 → Fin 2` is `c (σ 0) exp(−Z‖x‖)`, represented in actual complex
Lebesgue L². The spin map is linear and injective. Both standard spin columns
are proved linearly independent and satisfy the actual Hamiltonian graph at
energy `−Z²/2`. Every spin combination belongs to the intended H² domain.
The exact scalar normalization is
`‖exp(−Z‖x‖)‖₂² = π/Z³`.

This is a fully formalized mathematical result, with successful exact-source
compilation and axiom audits. It does not assert scalar simplicity, exact
ground-state multiplicity, full-spin uniqueness, an N ≥ 2 eigenpair, or full
Theorem T. The closed-form hydrogen energy is classical mathematics; no
mathematical novelty claim is made. This checkpoint records a concrete
formalization linked to the project’s physical continuum definitions.

## Proof dependencies and changes

`HydrogenRadialLp_v1.lean` proves L² membership of the exponential and its
Coulomb quotient directly by Haar radial integration. The three-dimensional
radial factor `r²` cancels the squared quotient singularity on `r > 0`.
Nonzero L² membership follows from continuity and positivity, using full
support of Lebesgue measure. No smoothness at the origin is asserted.

`HydrogenRadialBounds_v1.lean` proves uniform bounds for the regularized
first- and second-derivative coefficients, including the Hessian bound
`Z² + 2Z/r` away from the origin. The separate parent-owned calculus,
domination, limiting weak-derivative, and trace modules identify those
formulas and prove the actual scalar H² graph eigenpair in
`HydrogenEigenGraph_v1.lean`.

`HydrogenRadialNorm_v1.lean` proves the exact radial integral
`∫ exp(−a‖x‖) dx = 8π/a³` for `a > 0`, including the actual unit-ball volume,
and deduces the L² normalization. `HydrogenSpinStructure_v1.lean` packages the
two spin labels and proves injectivity and independence. The generic
`EigenRayleighUpper_v1.lean` explicitly assumes a nonzero actual graph
eigenvector, normalizes it, and obtains the variational upper bound. In the
final hydrogen theorem this hypothesis is discharged by the separately
proved explicit eigenvector. The existing sharp lower bound and spectral
identification then yield the exact ground energy.

## Evidence and reproducibility

All nine sources owned by this branch have exact-source successful receipts
in `HYDROGEN_RADIAL_SPIN_BUILD_PROVENANCE_v1.json` (SHA-256
`943baa2f777f1697a3865bd06c2941c0fb91f824ae9fd3af5291ed826a4316fb`).
The final theorem source `../lean/HydrogenSpinGround_v1.lean` has SHA-256
`22fc22f2b7ff2f2364f20119f4f9efd89a6c121e0f93dd30d8539173f5667e5c`.
The final audit `../lean/HydrogenSpinGroundAudit_v1.lean` has SHA-256
`33f6cccd9e5179d2682b17ee23ef6c63ffc63f466d6d842b33e3b27e20ca8f50`.

Every audited theorem depends only on `propext`, `Classical.choice`, and
`Quot.sound`. No additional mathematical axiom, `sorry`, `sorryAx`, native
decision trust mechanism, or assumed hydrogen eigenpair occurs in the final
composition. Readable audits expose definitions, typed function arguments,
and exact final hypotheses; `pp.proofs false` suppresses proof bodies and
proof-valued arguments only.

The parent’s independent exact-source review is
`../audits/HYDROGEN_RADIAL_SPIN_INDEPENDENT_REVIEW_v1.json`, SHA-256
`a443c6be6448cdaf844979e3a3402462bd7932d0e077fabd703232d5ce140dbc`.
It matched ten source hashes to successful receipts and found no issue.
This review supplements the proofs; agreement is not a proof.

Development used Lean `leanprover/lean4:v4.34.0-rc2` and pinned mathlib commit
`d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`, reusing existing dependency oleans.
For example, from the workspace root:

```sh
python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py HydrogenSpinGroundAudit_v1
```

The new targets were sent to the independent source-rebuild workstream.
This checkpoint does not attest an isolated rebuild of this latest branch;
consult the later reproduction record for that result. Failed development
attempts and their receipts remain preserved.

## Preservation and next active obligation

All work is new under the versioned continuation directory. Frozen baseline:
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. No frozen artifact was edited.

The next assigned obligation is an actual rational one-electron energy
solver for finite integer `Z` and requested precision `p`, including `Z=0`,
linked to the spectral theorem. The independent solver agent is constructing
that procedure. The many-electron program, particularly the original
two-electron analytic and spectral-separation obligations, remains active.
