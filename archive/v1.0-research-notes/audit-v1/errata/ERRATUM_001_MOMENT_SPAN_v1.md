> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

ISSUE ID: POST-FREEZE-2026-09-09-001
DISCOVERY DATE: 2026-09-09
FROZEN FILE: THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/THEOREM_T_COMPOSITION.md
FROZEN SHA-256: 1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da
LINE / THEOREM: Line 49; related coefficient terminology at lines 42, 71, 166
SEVERITY: NOTE
DESCRIPTION: The phrase “three-dimensional moment field” misnames a rational linear span represented by three rational coefficients. Field closure is false; independence of the evaluated constants is not needed or established. Frozen provenance is commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, annotated tag theorem-t-proof-freeze-2026-09-09. This is a terminology error, not a demonstrated failure of the moment algorithm or Theorem T.
DOWNSTREAM DEPENDENCIES: Exact-moment representation and coefficient-height descriptions in Theorem T composition; no used arithmetic operation requires the erroneous field property.
PROPOSED CORRECTION: Use “rational linear span” and distinguish the coefficient space Q^3 from its evaluated image; retain all actual algorithms and proof obligations.
CORRECTION FILE: THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/errata/MOMENT_SPAN_CLARIFICATION_v1.md
CORRECTION SHA-256: e28aa172042612cb9225111a0366f311c26c3beca082926346d22353e58a3ef9
STATUS: Terminology correction documented in a new external file. Frozen original unchanged. No substantive theorem status upgraded. Completed entry; future changes require a new dated entry.
