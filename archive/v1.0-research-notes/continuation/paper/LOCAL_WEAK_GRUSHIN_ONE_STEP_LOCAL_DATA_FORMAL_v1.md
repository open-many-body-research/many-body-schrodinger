> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# One-step weak Grushin gain from local L² data

For P_c = −Δ_y − c|y|²Δ_t on R⁴ × R^κ, with κ any finite index type and c > 0, the new theorem proves actual cutoffwise anisotropic regularity from a local weak equation. Let Ω be open and let χ be a smooth compactly supported real cutoff with support in Ω. There exist a compact K, with supp χ ⊆ K ⊆ Ω, and a nonnegative real constant C, both chosen before the input and forcing functions.

For all complex-valued raw functions g,h locally in L² on Ω satisfying ∫(P_c φ)g = ∫φh for every real smooth compact test supported in Ω, there are actual global L² classes U, g_y,i, g_t,j, and h_yy,ij such that U = χg almost everywhere and

D_y,i U = g_y,i, D_t,j U = g_t,j, D_y,j g_y,i = h_yy,ij

in the genuine compact-test weak sense. Define F = ∫_K |g|² and M = ∫_K |h|². The estimates are

- Σ_i ‖g_y,i‖² ≤ 2CF + (3/4)C(F+M).
- Σ_j ‖g_t,j‖² ≤ C(F+M)/(16c).
- Σ_i Σ_j ‖h_yy,ij‖² ≤ (3/2)C(F+M).

The YY sum contains all 16 ordered pairs. These conclusions introduce no global L² hypothesis on the raw functions and no input derivative, H², approximation, or spectral premise. They do not assert full joint H² or unweighted TT derivative control. The theorem treats scalar complex functions; finite spin-component composition and model-specific KS application are additional steps.

The proof first chooses compact K and an open V with supp χ ⊆ V ⊆ K ⊆ Ω, then takes the constant supplied by `local_weak_grushin_cutoff_one_step` on V. Only afterwards does it introduce g,h. The compiled compact indicator extension supplies global L² classes G,H, the same equation on V, and the exact identities ‖G‖²=F and ‖H‖²=M. Applying the global-L² local gain gives the weak jets. Since χ vanishes outside K, its product with G equals its product with raw g almost everywhere. This last step uses no derivative of an indicator and changes none of the constants. The ONB/coefficient-function identification is proved by `EuclideanSpace.basisFun_apply`, so the actual spectator Laplacian is preserved.

Evidence: `LocalWeakGrushinOneStepLocalData_v1.lean` compiled with SHA-256 `d1c5ead28bbe1632a5390be2d915565d52fdca6eef16931c99966c91584dd2f2`. Strict audit `audits/formal_semantics/20260910T175527_051096Z/receipt.json` prints the exact final statement and reports only `propext`, `Classical.choice`, and `Quot.sound`. Its report is complete, contains no printer ellipses, and records unchanged source/object hashes. The expanded statement was inspected specifically for K,C preceding all raw inputs, actual local integrals, genuine L² output classes, and absence of derivative premises.

This composes the separately compiled main gain source `LocalWeakGrushinOneStep_v1.lean` (SHA-256 `322b1fc6716c2ea9b66bb1c510dbd21a8f712b8d8d85403aa1448c7f1c2f8f5a`) with the sealed local extension checkpoint `GRUSHIN_LOCAL_L2_EXTENSION_CHECKPOINT_v1.json`. It is a fully formalized mathematical regularity theorem, not a numerical algorithm. Neighborhoods, witnesses and C are mathematical existence results; no computable dependence of C is claimed. No novelty claim is made.

Checks use Lean 4.34.0-rc2 and the disclosed pinned object cache. These new sources are outside the v19 source-rebuild snapshot, and this checkpoint makes no isolated source-rebuild claim for them. Run `check_module_v2.py LocalWeakGrushinOneStepLocalData_v1` followed by `audit_final_statements_v3.py LocalWeakGrushinOneStepLocalData_v1` from their existing continuation directories to reproduce the module and strict audit against that environment.

Frozen preservation anchor: original `rwa_proof/RWA_THEOREM.md`, SHA-256 `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. No prior successful or frozen bytes were edited.

Next: compose a locally continuous potential through the actual forcing g−Bf, then build the derivative induction needed for stronger local regularity. Quantitative analytic recurrence, physical KS application, and full Theorem T remain separate obligations.
