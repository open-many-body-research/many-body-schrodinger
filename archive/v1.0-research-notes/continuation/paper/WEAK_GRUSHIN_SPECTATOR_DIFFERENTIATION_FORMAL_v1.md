> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Genuine weak spectator differentiation of the Grushin equation

Evidence category: formal mathematical implication for actual local L² data
and compact-test weak derivatives. No second derivative of the solution is
assumed. This is a prerequisite for a second regularity step, not that step's
completed regularity conclusion.

Let X=R^4×R^m with product Lebesgue measure and let
P_c=-Δ_y-c|y|²Δ_t. The commutation theorem permits every real c, every spectator
direction v∈R^m, and every set Ω. For the intended PDE application Ω is open.
Let G,d,h,k be complex functions locally L² on Ω in the actual compactwise
sense. Assume the three genuine compact-test equations on Ω:

D_(0,v) G=d, P_cG=h, D_(0,v)h=k.

Then P_cd=k on Ω, with integrable left and right pairings for every real smooth
compact test supported in Ω. A separate specialization takes G,d as actual
whole-space L² classes and the first relation as
`WeakProductL2Directional G d (0,v)`; h,k remain raw locally L² functions.

The smooth proof establishes

P_c(D_(0,v)φ)=D_(0,v)(P_cφ).

It proves the required third-derivative permutation from second-derivative
symmetry, and proves directly that the spectator derivative of c|y|² vanishes.
Its smooth statement allows an arbitrary finite family of spectator
directions in an arbitrary real normed spectator space. The weak theorem uses
the actual orthogonal coordinate family in R^m.

Both P_cφ and D_(0,v)φ are smooth, compactly supported, and have support inside
supp φ. The weak proof is the exact chain

∫(P_cφ)d = -∫D_(0,v)(P_cφ)G
          = -∫P_c(D_(0,v)φ)G
          = -∫D_(0,v)φ h
          = ∫φ k.

Thus the differentiated equation is derived by testing the original equations;
no general distribution-commutation axiom or unproved second weak derivative
is inserted. All raw local L² compact pairings have separate integrability
proofs. The local L² assumptions on G,h are retained even though the equality
algebra itself only consumes their weak-test equations.

Four modules / nine declarations are recorded in the checkpoint
`audits/WEAK_GRUSHIN_SPECTATOR_DIFFERENTIATION_CHECKPOINT_v1.json`, with source and
object hashes and complete expanded-statement/axiom audits. Only propext,
Classical.choice and Quot.sound occur among the allowed foundational axioms.
The final proof sources were read directly, including an independent check of
the signs, test supports, and the exact derivative hypotheses.

Development checks reuse pinned cached Mathlib and previously compiled
continuation dependencies under Lean 4.34.0-rc2. These modules postdate the
completed 671-target desktop isolated source rebuild and have not yet been
included in a new isolated source rebuild. No executable derivative algorithm,
complexity bound, novelty, analytic regularity, or full Theorem T is claimed.

The preserved original claim source is `RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, frozen at
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`, snapshot
`THEOREM_T_FREEZE_2026-09-09_212604/`. No frozen artifact or prior successful
proof was modified.
