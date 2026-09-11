> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# PairKSPotentialAnalytic_v1 exact checkpoint

The exact pairKSLift is ContDiff at omega and AnalyticAt everywhere. For every real Z,E, the exact pairKSPotential Z E is ContDiffAt at omega and AnalyticAt at every point of the existing pairKSCoefficientPatch, hence AnalyticOnNhd on that patch. The patch assumes precisely both physical nuclear positions are nonzero; no y≠0 or pair separation is required, so the pair collision fiber away from the nucleus is retained.

Independent read-only focused source review by /root/test_extension_recovery found no hypothesis defect: actual pairCoordinates and ksMap retained, ContDiff omega rather than infinity, inverse nuclear norms justified exactly by hq.1/hq.2, polynomial squared Y norm, arbitrary real Z,E, no altered coefficient, PDE or all-order constant claim. The reviewer did not run a compiler; the v6 audit below supplies compiler evidence.

Reuses preserved KSMapAnalytic_v1 source SHA-256 `f90dd7a633543290ef173889bf126e5ac7d4ebde9291bc7278e20d795815794a` and PairKSPotentialSmooth_v1; neither was edited or rebuilt. Compiler PASS on first attempt via check_module_v2.py, using pinned dependency objects. Approved v6 audit PASS: audits/formal_semantics/20260910T220415_439881Z/receipt.json. All 5 expanded statements and complete axiom reports read; only propext, Classical.choice, Quot.sound, no forbidden tokens, printer ellipses, failures, fallback or omissions. Source and object unchanged during audit.

Source SHA-256: `07a0c974ade69a672fe0ba64c09d31b5aff53876170ea87161e00b42788e5355`.
Object SHA-256: `1b1704499a3ff9802ad038300a3b4e01efa26d8e595f8f7a9d7f65947963be24`.

This is actual coefficient analyticity, with the original pair coordinates and Hamiltonian expressions unchanged. Compact all-order estimates and scaled physical coefficient composition are separate. No computable constant or original T02 verification is claimed. Existing PASS sources, frozen artifacts, historical audits and shared ledgers were preserved.

Historical context: frozen relative path `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`, recorded in `THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`.
