> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual quadratic Y-word derivative bounds

Created 2026-09-10. This is a coefficient derivative prerequisite, not a
solution regularity theorem. Original T02 remains unverified.

Historical context: frozen `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, from
`THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`; frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. No frozen or previous PASS artifact changed.

## Exact scope

The new module `lean/GrushinQuadraticYWordBound_v1.lean` uses the existing
`directionalWordDeriv`, `yDir`, `Space kappa`, and scalar function
`q ↦ ‖q.1‖^2`. It proves the following actual formulas:

- The empty word gives `‖y‖^2`.
- Word `[i]` gives `2 * inner(oscillatorBasis i, y)`.
- Word `[i,j]` gives the constant
  `2 * inner(oscillatorBasis j, oscillatorBasis i)`.
- Every word of length at least three gives zero.

On any region with `‖y‖ ≤ R`, separate norm bounds are `R^2`, `2*R`, and `2`
for orders zero, one, and two. For `R ≥ 0`, every finite word is bounded by
`grushinQuadraticYWordBound R = R^2 + 2*R + 2`.

The on-region API is `grushin_quadratic_y_word_bound_on hR hOmega` in
`TheoremT.Continuum.WeakGrushin`. It requires no assumed quadratic derivative
bound, no openness or compactness, and no solution derivative family. The
all-word conclusion applies to this specific quadratic polynomial because
its derivatives vanish after order two.

## Verification

Compilation PASS:
`logs/development/GrushinQuadraticYWordBound_v1-20260910T212315_505862Z.json`.
The compiler reports only unused `DecidableEq` section-variable warnings in
two elementary formula lemmas.

Strict v5 audit PASS for all 12 declarations:
`audits/formal_semantics/20260910T212327_478050Z/receipt.json`.
Exact expanded statements were reviewed. There are no forbidden source tokens,
printer ellipses, or unexpected axioms; source and object were unchanged.
Every declaration uses only `propext`, `Classical.choice`, and `Quot.sound`.

- Source SHA-256: `e457e39732092c767a58a8acddc5d142b6af2528297b2563aa833673c0aac4ca`.
- Object SHA-256: `60151ca536778ba908e7a22312375d5d6f0cb77f51c3cbc06f956eacd670fa1e`.
- Expanded audit source SHA-256: `960fc002f9d5aca43c49585cf8dddbbd79456a295924fe53cc65b213e74bb38f`.
- Expanded audit log SHA-256: `6f8add65e1d27fae48ece72ff2d29fd978dd63d254409fc9ac9e6acdf27f642d`.

This reused pinned dependency objects without rebuilding their sources. It
does not prove any weak derivative existence, finite PDE induction, H12 norm
estimate, analytic coefficient estimate, or original T02 claim.
