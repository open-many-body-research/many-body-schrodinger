> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual local H² of physical nuclear KS pullbacks

For any finite electron count N and any selected electron i, the actual scalar
Coulomb eigenfunction graph, together with a continuous representative g,
implies that g composed with the actual nuclear KS lift belongs to local weak
H² on `nuclearKSCoefficientPatch i`. The formal conclusion constructs, for
every smooth compact cutoff in this open set, an actual complex L² class and
all first and ordered second L² weak derivatives tested against all smooth
compact real test functions. No derivative of the pullback is an input.

The domain includes y=0, the selected electron–nucleus collision. It excludes
other nuclear collisions and all pair collisions. This theorem makes no claim
at intersections with those excluded strata. The principal operator is exactly
−Δ_y−4|y|²Δ_t, with the previously proved physical analytic potential B.

The proof first gains Y and T derivatives and ordered YY derivatives from the
actual local weak equation. A second application to each spectator derivative
uses `(P+B)D_tG=−(D_tB)G`. Nested cutoffs recover diagonal TT derivatives;
the actual product Laplacian converse then constructs all mixed derivatives.
Outer plateau localization removes every derivative assumption on the original
locally L² input. This is why the known failure of a single gain to imply joint
H² does not affect the present two-gain argument.

For an actual full-spin fermionic eigenvector, a single locally Lipschitz
representative is selected with the established simultaneous spatial and spin
permutation law and pointwise spin norm bound. Every selected nuclear KS
pullback of every spin component has the stated local H² regularity.
The actual eigenvector graph is an explicit hypothesis; attainment or binding
for arbitrary N and Z is not inferred from this regularity theorem.

Both final statements compile and pass expanded-statement and complete axiom
audits with only `propext`, `Classical.choice`, and `Quot.sound`. Development
builds reuse pinned dependencies. These two sources postdate the immutable
v20 desktop rebuild capsule and therefore are not covered by that rebuild.
Noncomputable choices supply mathematical witnesses, not an executable solver.

Quantitative scale-uniform H² constants, factorial estimates, descent, the other
collision strata, and the unchanged trial dictionary approximation remain
separate obligations. Full Theorem T remains unverified.

Historical claims are preserved at frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. The frozen `RWA_REPORT.md` SHA-256 is
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
