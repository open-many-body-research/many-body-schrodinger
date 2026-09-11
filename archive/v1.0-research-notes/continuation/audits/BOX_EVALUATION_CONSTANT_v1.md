> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

ISSUE ID: R24-BOX-EVALUATION-CONSTANT-v1
DISCOVERY DATE: 2026-09-11
FROZEN FILE: rwa_proof/THEOREM_T_COMPOSITION.md
FROZEN SHA-256: 1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da
LINE / THEOREM: R24 rectangular point-evaluation constant; no frozen theorem modified
SEVERITY: NOTE
DESCRIPTION: Defines the real geometry-only constant E(a,b) as the inverse square root of the product side-length volume times the product of one plus each side length. Positive side lengths imply E>0 and E equals the product of the factors inverse sqrt(length) plus sqrt(length). For Fin 7 with the first four side lengths Ly and last three side lengths Lt, the exact constant is (inverse sqrt(Ly)+sqrt(Ly))^4 times (inverse sqrt(Lt)+sqrt(Lt))^3. No function, center, derivative order, or analytic estimate is an input to this algebraic identity.
DOWNSTREAM DEPENDENCIES: Geometry-only corollaries of the genuine seven-coordinate L2 point-evaluation theorem. Weak representative recovery remains separate.
PROPOSED CORRECTION: Add this algebraic constant module outside the frozen snapshot. Frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09, manifest THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json.
CORRECTION FILE: THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/BoxEvaluationConstant_v1.lean
CORRECTION SHA-256: 47b590a7b620a4bf504f9d1b3e4a6aa37180f1105fa258b4ae5d89a052d3599e
STATUS: Compiler PASS, approved strict v7 PASS for all four declarations; full expanded statements and constant definition read. Independent exact-source review by /root/finite_affine_jets found no defect in positive square-root factorization, inverses, individual factor identity, or the exact four/three index split. Receipt THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/formal_semantics/20260911T000718_410393Z/receipt.json, SHA-256 e1b79e584965a5ce403b1708b745b44badaaa7584bb0a7ea4f0d7620f713664e. Standard foundational axioms only, no printer diagnostics, unchanged source/object. Pinned cached dependencies reused without a source rebuild. Original T02 remains unverified.
