> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local weak H² for Grushin equations with forcing

Evidence category: fully compiled and axiom-audited continuum mathematical
implication. This is a separately identified extension of the homogeneous H²
result; it preserves that earlier theorem and proof unchanged.

Let X=R^4×R^m with actual product Lebesgue measure, c>0, Ω⊂X open, and B:X→R
smooth on Ω. Let G,F:X→C be locally L² on Ω. For every spectator coordinate
j, suppose an actual locally L² function J_j represents the weak derivative
D_tj F against every real smooth compact test supported in Ω. If

(P_c+B)G=F, where P_c=-Δ_y-c|y|²Δ_t,

holds against those same genuine compact tests, then G has actual local weak
H² on Ω. No weak derivative of G is an input hypothesis. No derivative of F
in the nuclear coordinates y is assumed.

The conclusion `ProductLocalWeakH2On G Ω` supplies, for each smooth compact
cutoff χ supported in Ω, an actual global product-measure L² representative
U=χG, first weak derivatives in all directions, and all ordered second weak
derivatives, including mixed directions.

The first gain applied to a smooth outer cutoff of raw G supplies actual
selected first Y/T and second YY derivatives. The local equation on a plateau
retains the original raw forcing F and its weak derivative tests. Genuine weak
spectator commutation and the local potential product rule give

(P_c+B)(D_tj G₀)=J_j-(D_tj B)G₀.

This forcing is locally L². A second first-gain application, nested single
weak-direction cutoff calculus, and the product Laplacian converse recover all
ordered second derivatives of the inner cutoff. The raw wrapper discharges
all selected derivative premises of the intermediate theorem. Restriction of
F,J_j and their test equations to the smaller plateau is explicit.

The endpoint does not quantify H² constants and does not assert smoothness,
analyticity, an algorithm, complexity, novelty, or full Theorem T. In particular,
it does not assert H² for arbitrary merely L² forcing without the stated weak
spectator derivative assumptions. The witnesses are mathematical existence
objects, not executable differentiation.

The two endpoint modules, exact source/object hashes, and full expanded
statement/axiom receipts are recorded in
`audits/LOCAL_WEAK_GRUSHIN_FORCED_H2_CHECKPOINT_v1.json`. Only propext,
Classical.choice and Quot.sound occur as foundational axioms. Both final
sources were read directly, with attention to the source derivative
hypotheses, plateau restriction, shared cutoff representative, and the absence
of input mixed or TT derivatives. Lean 4.34.0-rc2 and pinned cached dependencies
were used. The modules postdate the completed 671-target desktop isolated
source rebuild and have not yet been included in a fresh isolated source
rebuild.

Preserved original source: `RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`, snapshot
`THEOREM_T_FREEZE_2026-09-09_212604/`. No frozen or earlier successful artifact was
modified.
