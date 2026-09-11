> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exact hydrogen ground energy in the actual continuum spin space

Evidence: **formal mathematical theorem**, with compiled literal weak-domain statements, axiom dependencies and independent semantic reviews. This checkpoint establishes a one-electron component of S01; the full two-electron Theorem T remains unverified.

For every real charge Z>0, define f_Z(x)=exp(-Z|x|) on the original Configuration 1 = EuclideanSpace R (Fin 1 × Fin 3). The new sources prove:

- f_Z represents a nonzero actual complex L2 vector, with squared norm pi/Z^3.
- f_Z belongs to the unchanged weak H2 domain, including every ordered mixed second derivative.
- The original Coulomb graph satisfies H_(1,Z) f_Z = -(Z^2/2) f_Z, with H_(1,Z)=-Delta/2-Z/|x|.
- In the complete fermionic spin space, the original normalized H2 variational infimum, the actual H1 form infimum, and the actual operator spectral infimum all equal -Z^2/2.
- The map c in C^2 to the spin function sigma ↦ c(sigma(0)) f_Z is injective and every image is an actual H2 graph eigenvector at that ground energy. Its two basis columns are linearly independent.

The last statement establishes at least two independent full-spin ground vectors. It does not assert an upper bound on ground multiplicity or a unique full-spin vector.

## The nucleus is part of the weak-domain proof

For delta>0, the regularized profile exp(-Z sqrt(|x|^2+delta)) is globally smooth. Write s=sqrt(|x|^2+delta). Its first derivative is

    D_k f_delta = (-Z x_k/s) f_delta,

and every ordered mixed derivative is

    D_l D_k f_delta =
      (Z^2 x_k x_l/s^2 - Z delta_kl/s + Z x_k x_l/s^3) f_delta.

The first profile is dominated by Z f_Z. Off the null origin, each second profile is dominated by (Z^2+2Z/|x|) f_Z. Direct radial integration proves both f_Z and f_Z/|x| belong to L2 before any Sobolev membership is asserted. Thus the derivative domination does not use the conclusion it is meant to prove.

`ClassicalWeakLimit_v1` proves convergence against every real compactly supported smooth test, using classical integration by parts followed by dominated convergence. Applied to the profiles and then to their first derivatives, it supplies all nine actual weak second derivatives. This is stronger than checking the differential equation away from the nucleus: the uniform integrable majorants justify the distributional passage across it. No claim of classical C2 regularity at the origin occurs.

Summing the diagonal formulas gives Delta f_Z=(Z^2-2Z/|x|)f_Z almost everywhere. The exact Config 1 norm and empty electron-pair sum identify the existing potential with -Z/|x|. The scalar graph equation then follows with the original kinetic factor one half.

The ground energy is obtained from two proved inequalities: the actual nonzero eigenvector gives a normalized variational upper bound, and the previously formal nuclear lower bound at N=1 gives the reverse inequality. The previously formal H2/H1/spectral identifications then yield the actual spectral result. No spectral energy definition is silently replaced by a selected eigenvalue.

## Source and evidence record

The principal results are in:

- `../lean/HydrogenWeakDerivatives_v1.lean`, SHA-256 `d5fba2aa2bb10dbf9410ac8708487660595db2ad4259c4ca54b452b0a02298d3`.
- `../lean/HydrogenEigenGraph_v1.lean`, SHA-256 `5c0179d8508be578a90d6db00cd9e9d9535024edfcc003a9571211ae40ea319b`.
- `../lean/HydrogenSpinGround_v1.lean`, SHA-256 `22fc22f2b7ff2f2364f20119f4f9efd89a6c121e0f93dd30d8539173f5667e5c`.

`HYDROGEN_FORMAL_BUILD_PROVENANCE_v1.json`, SHA-256 `5344634e275f632685c52b1a9eadf7ea0f0fe14dd0cd71b933b349c619117a10`, records 22 exact successful source builds and 74 printed axiom reports, including repeated audit reports. They use only propext, Classical.choice and Quot.sound. No sorry, added mathematical axiom or native evaluator proof is used.

The preferred literal scalar audit is `HydrogenScalarSemanticAudit_v2.lean`, SHA-256 `a24c8129acffdd85b138fbef908da173197a857b6c42935a4ac81ef6c4c99095`. It displays the actual complex Lebesgue L2 witnesses, every compact-test equation, the explicit radial profile and norm, and the unsoftened Coulomb output. Its mathematical statement has no printer elisions; only the proof body is suppressed. The earlier successful print artifacts remain preserved.

Independent reviews cover both the weak assembly and the separately authored radial and spin components. Their exact hashes and successful source receipts are linked by the provenance. Agreement of reviewers is additional scrutiny, not the kernel proof itself.

Builds used Lean `leanprover/lean4:v4.34.0-rc2`, mathlib commit `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`, and pinned dependency objects. From the workspace, the per-module build command is:

    python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py MODULE

The earlier isolated source rebuild of 145 foundation targets predates this hydrogen extension. The new hydrogen closure has not been represented here as independently source-rebuilt. This is an explicit remaining reproduction task, separate from the successful current-environment compilation.

## Frontier and next executable actions

The active follow-on is an actual exact rational one-electron energy procedure for finite inputs Z,p, proved against the actual spectral infimum, including Z=0 through the already formal nonpositive-charge result. It has its own source, execution and trust obligations.

For the two-electron spectral comparison, hydrogen excited energies, a suitable complement lower bound, and the actual two-electron comparison/trial premises remain separate obligations. No positive gap, exact scalar multiplicity or full hydrogen spectral decomposition follows merely from the ground eigenpair. The new result is a formal realization of the explicit 1s profile; no mathematical novelty claim is made.

Frozen baseline commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The unchanged actual continuum definitions come from `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/lean/ContinuumFoundation_v1.lean`, SHA-256 `4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e`. All new work uses versioned continuation files; successful prior and frozen bytes were preserved.
