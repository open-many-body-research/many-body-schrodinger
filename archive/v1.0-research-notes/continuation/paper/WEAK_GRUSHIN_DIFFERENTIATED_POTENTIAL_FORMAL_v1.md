> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual weak differentiation of a Grushin equation with potential

On R⁴ × R^κ, write P_c=−Δ_Y−c|y|²Δ_T, with c any real number. Let Ω be open
and B a real function C∞ on Ω. Let G,d be actual complex L² classes on the
ordinary Cartesian product, with d the genuine weak derivative of G in
spectator direction (0,v). Only this first derivative is input.

`weak_grushin_homogeneous_potential_spectator_differentiate` proves that the
actual local weak equation

    (P_c+B)G=0

implies

    (P_c+B)d=−(D_(0,v)B)G.

The new forcing is proved locally L² on Ω. For every real smooth compact
joint test supported in Ω, the theorem concludes both test-integrand
integrability statements and the exact differentiated weak equation.

The inhomogeneous theorem
`weak_grushin_potential_spectator_differentiate` additionally permits raw
complex forcing functions F,J that are only locally L² on Ω. It explicitly
assumes the genuine local weak relation D_(0,v)F=J. From (P_c+B)G=F it proves

    (P_c+B)d=J−(D_(0,v)B)G,

with local L² membership and compact-test integrability of this forcing.
The derivative of F is an input hypothesis; it is not inferred merely from
the original equation.

The proof first uses the proved potential reduction to write P_cG=H, where
H=−BG in the homogeneous case and H=F−BG in the inhomogeneous case. The
proved local potential Leibniz rule gives the actual derivative of H:

    D_(0,v)H=−[Bd+(D_(0,v)B)G]

or J−[Bd+(D_(0,v)B)G], respectively. All intermediate sources are locally L².
The genuine weak spectator-commutation theorem then differentiates P_cG=H.
Finally the inverse potential reduction restores B on the left. The resulting
forcing has the signs shown above. Integral addition and subtraction are
used only after proving the requisite integrability.

The principal commutation is proved on actual smooth tests and lifted to the
weak equation. Its coefficient c|y|² is spectator-invariant. Consequently the
identity holds for every real c; the c>0 hypothesis needed for separate
coercive regularity estimates is not part of this differentiation theorem.
The exact equality between the concrete spectator coordinate basis and the
orthonormal basis used by the potential-reduction API is proved explicitly.

Neither theorem assumes H² regularity, second derivatives of G, a
differentiated equation, or global L² membership of BG. Smoothness of B is
required only on Ω. The hypotheses about G,d are global L² and their genuine
global first weak derivative, while the equations and coefficient regularity
are local. An outer cutoff can supply such witnesses in a later local-gain
composition; that construction is a separate obligation.

The new sources are `WeakGrushinDifferentiatedPotentialEquation_v1.lean` and
`WeakGrushinDifferentiatedPotentialForcing_v1.lean`. Their exact statements
compile and undergo strict expanded-statement and kernel-axiom auditing.
Only propext, Classical.choice, and Quot.sound occur. Pinned dependency
objects are reused. These new sources are outside the completed 671-target
desktop source-rebuild snapshot. The accompanying checkpoint records exact
hashes and references the previously sealed Leibniz and principal weak
differentiation dependencies.

This establishes a differentiation identity, not a second local regularity
gain, joint H² conclusion, analytic estimate, approximation rate, solver, or
full Theorem T.

Frozen historical reference: commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`,
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
Frozen and previously successful sources and receipts are preserved.
