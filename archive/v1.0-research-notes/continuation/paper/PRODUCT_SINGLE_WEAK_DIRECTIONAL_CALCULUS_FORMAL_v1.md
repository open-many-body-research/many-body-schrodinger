> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Product calculus from one genuine weak directional derivative

On the ordinary product Y×T of finite-dimensional real inner-product spaces,
with actual product Lebesgue measure and complex L² classes, let D_v f=d be a
genuine weak directional derivative against every real smooth compact test.
For every real smooth compact cutoff η, the formal theorem constructs L²
classes U,a satisfying

U=ηf almost everywhere,
a=ηd+(D_vη)f almost everywhere,
D_vU=a in the same genuine compact-test sense.

Only this one input derivative is assumed. No derivative in another direction,
full H¹ jet, or H² regularity is required. The proof lifts the actual L² classes
and cutoff through the measure-preserving WithLp 2 equivalence, applies the
already proved generic bounded smooth multiplier theorem, and transports back.
The compact support of η and D_vη supplies their actual L-infinity membership.
The formula is a proved equality of representatives, not a formal placeholder.

A second module proves zero, addition, negation, subtraction, multiplication
by real or complex constants, finite sums, and finite real linear combinations
for one fixed genuine weak derivative direction. The real and complex scalar
actions on the actual L² classes are explicitly identified.

Evidence: two compiled modules, ten declarations, complete final statement and
axiom audits with only propext, Classical.choice and Quot.sound. Sources and
objects are sealed in
`audits/PRODUCT_SINGLE_WEAK_DIRECTIONAL_CALCULUS_CHECKPOINT_v1.json`. The sources
were read directly; no all-direction or second-derivative hypothesis is hidden
in either conclusion. Lean 4.34.0-rc2 and pinned cached dependencies were used.
These new sources postdate the completed 671-target desktop source rebuild and
have not yet been included in a fresh isolated source rebuild.

The immediate use is a nested-cutoff second derivative construction. This note
does not itself assert that second derivatives of the original input exist.
It supplies mathematical L² objects, not executable differentiation, certified
numerics, complexity, analyticity, novelty, or full Theorem T.

Preserved source: original `RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`, snapshot
`THEOREM_T_FREEZE_2026-09-09_212604/`. All earlier successful and frozen artifacts
were preserved unchanged.
