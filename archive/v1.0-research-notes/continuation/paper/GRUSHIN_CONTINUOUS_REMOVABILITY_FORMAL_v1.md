> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# A formal codimension-four removability theorem

For every finite electron count N and index i in Fin N, use the actual lifted
space R^4 × R^(3(N−1)) with product Lebesgue measure. Let v_j be any finite
family of spectator directions and let c be real. For real smooth test functions,
the formalized differential expression is

Q phi = −sum_(k=1)^4 D_(e_k,0)^2 phi
        −c |y|^2 sum_j D_(0,v_j)^2 phi + B phi.

Assume that B is real and continuous and that u and f are complex and continuous
on this whole lifted space. Let Omega be any subset. If

integral (Q psi) u = integral psi f

for every real C-infinity compactly supported test psi with topological support
in Omega minus {y=0}, then the same equality holds for every such test whose
topological support is in Omega. All integrals are actual Bochner integrals.
Their integrability is proved, using continuity and compact support.

This is `nuclear_KS_continuous_Grushin_removability` in
`lean/GrushinContinuousRemovability_v1.lean`. The earlier bounded version is
preserved in `lean/GrushinBoundedRemovability_v1.lean`.

## Proof and constants

The actual smooth cutoff is chi_delta(y)=1−b(y/delta), where b is a fixed
C-infinity bump equal to one on the unit closed ball and zero outside the ball
of radius two. First and ordered second coordinate derivatives are bounded by
C1/delta and C2/delta^2, for proved finite nonnegative constants. The derivatives
vanish outside the transverse closed ball of radius 2 delta.

The exact Frechet-derivative product rule gives

Q(chi_delta phi) = chi_delta Q phi
 −sum_k [(D_k^2 chi_delta) phi + 2(D_k chi_delta)(D_k phi)].

The spectator and multiplication terms commute with this cutoff. The remaining
commutator is continuous, compactly supported inside the test support, bounded
by A/delta^2 for 0<delta<=1, and zero outside the transverse radius-3-delta tube.
The spectator projection T of the test support is compact and has finite volume.
The exact transverse ball volume is pi^2 r^4/2. Thus a supported integrand bounded
by A/delta^2 has integral norm at most

81 A (pi^2/2) volume(T) delta^2.

This tends to zero. For continuous u, only its bound on the compact test support
is used; a global bound is unnecessary. The transverse zero set has measure
zero, chi_delta tends to one elsewhere, and 0<=chi_delta<=1. Dominated convergence
handles the two main integrals. The explicit sequence delta_n=1/(n+1) completes
the argument. No distributional extension or removability axiom is imported.

## Scope and evidence

The exact final statements compile in the pinned Lean environment. Complete
expanded-statement and axiom receipts accompany the checkpoint. The trusted
axioms are propext, Classical.choice and Quot.sound. Pinned library and previous
continuation objects are reused for development. These modules are outside the
392-target Colab rebuild snapshot, whose final result remains unobserved.
Independent agent review was unavailable because the agent usage quota was
exhausted. No independent source rebuild of these new modules is claimed.

This theorem proves the implication from an equation off the singular set to an
equation through it. It does not yet prove that the physical Coulomb KS pullback
satisfies that equation off the set. The physical representative's continuity
has already been proved separately. Establishing the actual weak pullback,
local coefficient applicability, higher regularity, and factorial estimates
remains necessary. The stronger paper-level L2-input removability statement is
not claimed here. No novelty claim is made.

## Preserved provenance

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Tag: theorem-t-proof-freeze-2026-09-09.
Frozen relative path: THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md.
SHA-256: 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066.
All frozen and previously successful sources remain unchanged.
