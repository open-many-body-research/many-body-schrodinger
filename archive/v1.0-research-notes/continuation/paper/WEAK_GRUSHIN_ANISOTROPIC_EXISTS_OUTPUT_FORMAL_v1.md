> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Eventual existential outputs for anisotropic closure

The new theorem
`TheoremT.Continuum.WeakGrushin.anisotropic_limit_of_eventually_exists_compact_outputs`
in `WeakGrushinAnisotropicLimitExistsOutput_v1.lean` accepts the uniform
approximation package in the form naturally produced by localized weak-H²
estimates. For each sufficiently large n it assumes existence of an L² output
H, full weak-H² witnesses d,e, and a compact support set K for the fixed input
u_n. It requires the actual global compact-test Grushin equation P_c u_n=H,
and bounds ||u_n||²≤F and ||H||²≤M. Strong L² convergence u_n→f and c>0 are
also hypotheses. No output sequence must be supplied in advance.

The theorem constructs genuine compatible first-Y, first-T, and ordered-YY
weak L² derivatives of f, with the same estimates as the previously sealed
actual-output closure:

    Σ_i ||D_Yi f||² ≤ 2F+3M/4,
    Σ_j ||D_Tj f||² ≤ M/(16c),
    Σ_i Σ_j ||D_Yj D_Yi f||² ≤ 3M/2.

The proof chooses one admissible H at each good index and assigns zero at
indices where no package exists, then applies the existing eventual closure
theorem. This is explicitly noncomputable analytic witness selection. The
zero values occur only outside the eventual good set and impose no additional
premise. No implementation, computable selection procedure, or numerical
solver is asserted.

This wrapper does not itself construct uniformly controlled localized
regularizations for an arbitrary local weak solution. It removes a witness
packaging inconvenience from that separate composition. The earlier
checkpoint and all its successful sources remain unchanged. The new source
compiles against pinned dependency objects and its complete expanded theorem
statement and kernel-axiom dependencies are strictly audited. The only axioms
are propext, Classical.choice and Quot.sound. It is outside the completed
671-target desktop source-rebuild snapshot.

The previous exact result and proof mechanism are recorded in
`WEAK_GRUSHIN_ANISOTROPIC_LIMIT_FORMAL_v1.md` and
`audits/WEAK_GRUSHIN_ANISOTROPIC_LIMIT_CHECKPOINT_v1.json`.

Historical frozen reference: commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`,
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
