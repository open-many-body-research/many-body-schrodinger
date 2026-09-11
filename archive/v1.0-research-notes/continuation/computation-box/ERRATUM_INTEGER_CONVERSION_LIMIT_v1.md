> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

ISSUE ID: CONT-COMP-001
DISCOVERY DATE: 2026-09-09
FROZEN FILE: THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md (underlying provenance only; the defect is in the explicitly identified post-freeze implementation below)
FROZEN SHA-256: 7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79
LINE / THEOREM: Post-freeze exact_box_v1.py encode/requested_width_schedule/box_enclose; BOX_SOLVER_v1.md requested-width procedure claim, in THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/computation/box/
SEVERITY: REPAIRABLE GAP
DESCRIPTION: The sealed exact_box_v1.py source SHA-256 f1358f9f63f025554128a20ad2d464934509a6363ae49bc028cba92e2673ad58 uses Fraction/string and JSON conversion without changing Python 3.14.7's default 4300-decimal-digit guard. The cheap finite call requested_width_schedule(1,1,Fraction(1,10**5000)) raises ValueError: "Exceeds the limit (4300 digits) for integer string conversion; use sys.set_int_max_str_digits() to increase the limit". Witness integer_string_limit_counterexample_v1.json records the declared runtime, default cap, exact call and exception. Consequently the unconditional arbitrary-finite implementation claim in that default runtime is incorrect. The mathematical unbounded-integer algorithm/termination argument is unaffected. All already emitted finite certificates remain valid and replay successfully. The same default conversion limitation applies to sufficiently large direct invocations of other earlier finite-stage scripts; their successfully emitted certificates are not invalidated.
DOWNSTREAM DEPENDENCIES: Claims of executable total requested-width behavior, arbitrary-finite integer input parsing, decimal rational endpoints, JSON certificates and source replay at unrestricted input sizes. No continuum inequality, matrix-entry proof, finite stage output, frozen theorem artifact or Lean theorem is changed.
PROPOSED CORRECTION: Preserve the old source and claim verbatim. Use the separately versioned exact_integer_runtime_v1.py policy before parsing, serializing or invoking prior mathematical routines: sys.set_int_max_str_digits(0) where the guard exists. The new general_box_enclose_v1.py imports this policy before argument parsing and all certificate work. State the arbitrary-length integer/finite-array computational model separately from available physical execution resources. No claim of infinite actual RAM or unrestricted running time follows.
CORRECTION FILE: THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/computation/box/exact_integer_runtime_v1.py
CORRECTION SHA-256: bbe4c9957057311e1f1dcd30deff31ee7322988770023555dc026ac4abf3190b
STATUS: Repaired in the new runtime entry point; original sealed source intentionally unchanged. integer_string_limit_repair_result_v1.json records PASS for the same call, 227823 serialized characters and exact rational JSON roundtrip. test_general_box_enclose_v1.py also executes a vacuum requested-width result with epsilon=10^-5000 and verifies its serialization. No nonzero-electron conservative scheduled execution is claimed.

Frozen commit: `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`.
Frozen annotated tag: `theorem-t-proof-freeze-2026-09-09`.

This is an append-only correction of a post-freeze implementation claim, not a
retroactive alteration of the frozen project or successful finite outputs.
