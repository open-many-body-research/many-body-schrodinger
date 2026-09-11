> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local weak H² of first spectator derivatives

For the actual product-measure Grushin operator P_c=-Δ_y-c|y|²Δ_t, let c>0,
Ω be open, and B be real and smooth on Ω. Let G and dT_j be actual global L²
classes satisfying genuine weak derivative identities D_tj G=dT_j against all
real smooth compact product tests. Assume the homogeneous local weak equation
(P_c+B)G=0 on Ω.

Then each dT_j has genuine local weak H² on Ω. This endpoint does not assume
global H² of G, any Y derivative of G, or any second derivative of G or dT_j.
The only input solution derivatives are the stated first spectator derivatives.
Every compact cutoff of dT_j has actual L² first and all ordered second weak
derivative witnesses.

The differentiated potential equation has forcing

R_j=-(D_tj B)G.

The new helper explicitly proves that R_j and the functions

J_jk=-[(D_tj B)dT_k+(D_tk D_tj B)G]

are locally L² on Ω, and that D_tk R_j=J_jk in the genuine compact-test sense.
This uses the actual local potential product rule with coefficient D_tj B. It
uses only the original given first weak derivative D_tk G=dT_k, and does not
use a derivative of dT_j. Hence the source hypotheses of the forced H² theorem
are established without assuming the desired bootstrap conclusion.

The previously proved exact weak differentiated equation gives
(P_c+B)dT_j=R_j. Applying the raw forced H² theorem to dT_j,R_j,J_jk yields the
result. The formal definitions use actual fderiv expressions for both first
and ordered second derivatives of B; J_jk is not an unspecified witness.

Evidence is two compiled modules and three declarations with a complete final
expanded-statement and axiom audit. Sources and objects are sealed in
`audits/LOCAL_WEAK_GRUSHIN_SPECTATOR_H2_CHECKPOINT_v1.json`. Only propext,
Classical.choice and Quot.sound occur as foundational axioms. Both final
sources were read directly, including the sign of the forcing derivative and
the derivative assumptions used by the forced theorem.

This is a finite qualitative bootstrap step, not a proof of arbitrary-order
smoothness, analytic regularity, factorial estimates, or full Theorem T. No
quantitative H² constant, executable differentiation, complexity, or novelty is
claimed. Lean 4.34.0-rc2 and pinned cached dependencies were used; these new
modules postdate the completed 671-target desktop isolated source rebuild and
have not yet been included in a fresh isolated source rebuild.

Preserved original source: `RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`, snapshot
`THEOREM_T_FREEZE_2026-09-09_212604/`. All earlier successful and frozen artifacts
were preserved unchanged.
