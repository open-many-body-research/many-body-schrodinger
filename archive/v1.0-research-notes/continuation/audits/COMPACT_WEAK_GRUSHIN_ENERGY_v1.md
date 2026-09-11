> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact weak Grushin energy — immutable checkpoint

ISSUE ID: POST-FREEZE-COMPACT-WEAK-GRUSHIN-ENERGY-v1
DISCOVERY DATE: 2026-09-10
FROZEN FILE: rwa_proof/THEOREM_T_COMPOSITION.md
FROZEN SHA-256: 1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da
LINE / THEOREM: Additional compact weak-H2 energy prerequisite; no frozen theorem edited.
SEVERITY: NOTE
DESCRIPTION: Proves the actual compact weak Grushin energy identity and Cauchy bounds on the ordinary product Space kappa, with four Y coordinates and arbitrary finite spectator coordinate set.
DOWNSTREAM DEPENDENCIES: Compact support graph estimates and subsequent local regularity arguments may use this prerequisite. Original T02 remains unverified.
PROPOSED CORRECTION: Add a separately compiled and audited proof module without modifying historical artifacts or claims.
CORRECTION FILE: THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/CompactWeakGrushinEnergy_v1.lean
CORRECTION SHA-256: 21dfe1d7d23034328d100b2263f7d1e62c30e0ca4f81669bf68dee16411f4a1d
STATUS: Compiler PASS; approved v7 strict statement/axiom audit PASS; focused independent source review complete.

The frozen source identity is recorded in `THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.

## Actual claim and hypotheses

The definition `weakGrushinGradientEnergy c d` is the sum of the actual squared L2 Y derivative integrals plus c times the actual squared L2 spectator derivative integrals weighted by the squared Y radius. The measures are the existing product Lebesgue measure.

The compact weak-H2 theorem assumes f in the actual L2 space, first derivative witnesses d in every constant direction, second derivative witnesses e in every ordered pair of constant directions, the genuine `WeakProductL2Directional` relations, and AE support of f in a specified compact K. It constructs the existing smooth approximation and its single larger compact support, proves principal L2 membership, and obtains the energy identity by the existing weighted limits specialized to the constant multiplier one. No identity, approximation sequence, derivative support, or convergence statement is assumed.

The principal coefficient c is any real number for the energy identity and Cauchy estimate. The nonnegativity and Y-gradient domination statements explicitly require c >= 0. The output corollary assumes the original compact smooth real-test equation for `splitGrushin c oscillatorBasis (fun _ => 0)` with complex L2 output h, and proves energy squared <= norm(f)^2 * norm(h)^2. The last theorem bounds the square of the sum of the Y derivative norm squares by that same product. Full weak H2 is an input; no regularity is inferred from the output equation alone.

## Verification

First compiler run passed with no diagnostic output using `check_module_v2.py`; source was preserved after this PASS. Object SHA-256: `c3893a1a9271e894c2faf759c28998fa6ba00aec3c5d547df8c67fa4f21c3424`.

Approved `audit_final_statements_v7.py` SHA-256 `473c8adfebd3c2ff78325f8d6c10a66ded375fdf8a8f32ad6ab9e6aaef564fb1` produced `audits/formal_semantics/20260910T233023_517437Z/receipt.json`. All nine expanded declaration types and their axiom reports were read. The defining source bodies were also read, including the energy definition. The audit reports complete axiom discovery, only propext/Classical.choice/Quot.sound, no forbidden source tokens, zero printer ellipses or failure/fallback/omission diagnostics, and unchanged source/object bytes.

The focused independent reviewer `/root/compact_h2_density/outer_cardinality` read the exact PASS source and reported no mathematical defect. The review checked the ordinary product measure, principal sign, constant multiplier one specialization, derived support of first/second approximant jets, weighted limits, principal L2 membership, and complex output identified through the original real-test equation. The reviewer did not compile, edit, or rerun the audit.

Pinned cached dependencies were reused; they were not rebuilt. No frozen source, previous PASS artifact, old audit, or shared ledger was changed. This checkpoint does not claim all-order solution regularity or completion of T02.
