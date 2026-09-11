> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact weak Grushin slab graph bounds

ISSUE ID: POST-FREEZE-COMPACT-WEAK-GRUSHIN-SLAB-GRAPH-BOUNDS-v1
DISCOVERY DATE: 2026-09-10
FROZEN FILE: rwa_proof/THEOREM_T_COMPOSITION.md
FROZEN SHA-256: 1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da
LINE / THEOREM: Compact weak graph estimates added as a separate prerequisite.
SEVERITY: NOTE
DESCRIPTION: Combines the actual compact weak energy identity, the exact-radius weak slab Poincare estimate, and proved nonnegative scalar cancellation.
DOWNSTREAM DEPENDENCIES: Local estimates may use these compact weak graph bounds. Original T02 remains unverified.
PROPOSED CORRECTION: Add this new module; preserve all frozen and prior PASS artifacts.
CORRECTION FILE: THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/CompactWeakGrushinSlabGraphBounds_v1.lean
CORRECTION SHA-256: 1a5345a9117c69b48da0d6f07afbcaa204f0798122317e8474ff9096d2b9db3a
STATUS: Compiler PASS and approved v7 strict statement/axiom audit PASS.

Frozen provenance: `THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`; commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`; tag `theorem-t-proof-freeze-2026-09-09`.

## Mathematical scope

Both theorems retain actual global weak H2 witnesses d,e for f, compact K with f zero almost everywhere outside K, complex L2 output h, the original all-compact-smooth-real-test equation `splitGrushin c oscillatorBasis (fun _ => 0)`, and c >= 0. For R > 0 and a chosen Y coordinate i, the first theorem assumes only the almost-everywhere support implication f(p) != 0 => abs(p.Y_i) <= R. The second theorem derives that implication from the coordinate bound on K itself.

The conclusions are the actual product-L2 inequalities norm(f)^2 <= (4 R^2)^2 norm(h)^2, weak energy <= 4 R^2 norm(h)^2, and the sum of the four squared Y-derivative L2 norms <= 4 R^2 norm(h)^2. The support radius is that of the original limiting function; the larger compact support used by the underlying approximation is absent from the constants. Cancellation includes the zero-energy case and does not divide by f or its energy.

The proof invokes the already sealed weak energy and weak Poincare results. It does not derive weak H2 from the output equation, remove the support hypothesis, prove a spectral gap for unrestricted functions, or establish all-order solution regularity.

## Validation

The final source compiled with `check_module_v2.py`, then remained unchanged. Its object SHA-256 is `6a4dc51146f362d2fd5047a8fbefb7bef44a4c5de019da59098ba28242c5c0ac`. One earlier failed elaboration record is retained; the repair only specified the finite summand function for `Finset.single_le_sum`.

Approved `audit_final_statements_v7.py` SHA-256 `473c8adfebd3c2ff78325f8d6c10a66ded375fdf8a8f32ad6ab9e6aaef564fb1` produced `audits/formal_semantics/20260910T233504_474904Z/receipt.json`. Both expanded statements and their axiom reports were read in full, alongside the exact source bodies. The strict receipt reports all expected declarations, standard foundational axioms only, no forbidden tokens, zero printer ellipses/failure/fallback/omission diagnostics, and unchanged source/object hashes. Pinned cached dependency objects were reused without a rebuild.

Independent reviewer `/root/local_elliptic_gain` read both exact theorem bodies and found no defect. The review checked nonnegative weak energy, actual squared source norm, the original limiting-function slab bound, exact weak-output Cauchy, the finite nonnegative Y sum, and the compact-K implication. No approximation support radius enters the constant. The reviewer did not compile or rerun the audit. No historical artifact or shared ledger was edited.
