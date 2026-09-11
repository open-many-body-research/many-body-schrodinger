> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact Grushin review and combined companion, v18

Date: 2026-09-10T15:49:19.892083+00:00. Reviewer: independent bounded subagent `grushin_review_v18`.

The original `compact_grushin_estimates` has no error identified within its stated smooth compact-support scope. This review inspected the exact source and expanded statement and 30 immediate/supporting Grushin, partial Fourier, and oscillator source files. It is not a repeated full-project audit. The machine-readable review records every inspected source hash in `COMPACT_GRUSHIN_ADVERSARIAL_REVIEW_v18.json`.

For finite spectator index type κ, the final hypotheses are exactly c ≥ 0, G : R⁴ × R^κ → C smooth, and compact support. The actual operator is P_c = −Δ_y − c|y|²Δ_t. Its coordinate derivatives are Frechet derivatives applied to the actual coordinate vectors, and all final integrals use product Euclidean Lebesgue measure. Intermediate transfer lemmas do have fiber inequalities as premises; the three physical final proofs discharge those premises through the oscillator lemmas.

The Fourier kernel is exp(−2πi〈t,ξ〉). Its oscillator parameter is a = 2π sqrt(c)|ξ|. The oscillator square identity is

    ||A_a u||² = ||Δu||² + a⁴ || |y|²u||²
                 + 2a² (|| |y|∇u||² − d||u||²).

Together with d²a²||u||² ≤ ||A_a u||², this gives

    d (||Δu||² + a⁴|| |y|²u||² + 2a²|| |y|∇u||²)
      ≤ (d+2)||A_a u||².

Thus the four-dimensional factor 3/2 bounds the sum of pure and mixed components. Independently, d=4 in the oscillator lower bound gives 16c||∇_t G||² ≤ ||P_c G||² after the Fourier derivative factors cancel. The c=0, ξ=0, and empty spectator-index cases involve no division. Weighted Plancherel requires only continuity of |y| in y; no invalid smoothness assertion at y=0 is used. The finite sums and integral exchanges prove their integrability hypotheses.

The reviewer added and compiled a strictly stronger companion in three new modules, preserving all sealed sources:

    ||Δ_y G||² + ||c|y|²Δ_t G||²
      + 2c ΣᵢΣⱼ || |y|D_tⱼ D_yᵢ G||² ≤ (3/2)||P_c G||².

This statement is `TheoremT.Continuum.compact_grushin_combined_bound`. Its exact coordinate order is D_t(D_yG); all norms are actual squared L² integrals. `EuclideanOscillatorCombinedBound_v1` proves the general finite-dimensional combined oscillator bound, `GrushinFourierCombinedBound_v1` supplies the exact mixed integral transfer and Fourier bound, and `CompactGrushinCombinedBound_v1` proves the full-space statement.

All five new declarations passed the strict expanded-statement/axiom audit at `formal_semantics/20260910T154706_782004Z/receipt.json`; only `propext`, `Classical.choice`, and `Quot.sound` occur. Current source/object hashes and the audit source/log hashes were rechecked. Existing pinned library, prior-audit, and continuation object caches were reused. This checkpoint is not an isolated source dependency rebuild. The reviewer constructed the companion after reviewing the inherited theorem, so the new proof still merits root review; agreement is not a substitute for kernel checking.

No weak-solution extension, localized gain, analyticity, factorial recurrence, sharpness, novelty, or full Theorem T is asserted. The next active obligation is localized energy/Caccioppoli control and weak Grushin gain.

Preservation reference: `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`; frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. This work is an extension, not a silent correction of that report.

Combined checkpoint: `COMPACT_GRUSHIN_COMBINED_BOUND_CHECKPOINT_v1.json`, SHA-256 `2ff63a16ca9cbf581dd25e961ea22d212fba67605574b22f076553ff395c44f8`.
Machine-readable review: `COMPACT_GRUSHIN_ADVERSARIAL_REVIEW_v18.json`, SHA-256 `832bab659f6a7e0403404a4bb877e23f82f7e6970619b6b3236c70d104f28187`.
