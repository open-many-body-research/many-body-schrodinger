> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit finite spectator reserve: adversarial review v1

Date: 2026-09-10. Reviewer: `/root/local_elliptic_gain/product_local_h2`.

**Finding:** no mathematical or semantic defect was found in the two reserve compositions. Their output derivatives are genuine weak derivatives on the cutoff plateau, with the displayed norm bounds. The finite spectator families and their common integral budgets remain explicit input hypotheses.

This was a bounded read-only review, with no compilation or changes to Lean sources. The coordinating agent reported the explicit reserve's first-compile PASS and a pending strict v5 audit. This note records semantic review, not a replacement for that audit. The reviewer authored the equation-source bound used below, so review of that component is not independent. Its completed strict receipt is `formal_semantics/20260910T193033_499001Z/receipt.json`. Reported module builds reused pinned dependency objects.

## Exact sources

All paths are relative to `../lean/` from this note.

| Source | SHA-256 |
| --- | --- |
| `WeakGrushinExplicitFiniteSpectatorReserve_v1.lean` | `79b29d7d3451e46f3a7043eef59a5affb61de35670d1339b390b6326153b60bd` |
| `WeakGrushinFiniteSpectatorReserve_v1.lean` | `609a4b09558f1fac3e726e4bf939540eb002d2620a0e2f7598e2963b99b1dd99` |
| `SpectatorWordEquationSourceL2Bound_v1.lean` | `2d420751848a04381cc9d20073cd384b40bb1aafbd4c38b4a2daaa8fef367892` |
| `LocalWeakGrushinExplicitPotentialOneStep_v1.lean` | `79516070954833a6433a759bf8a1b5b778a5d903eb312b321f7a66b6877c6e68` |

The two reserve sources and the exact one-step interface/proof were inspected. The equation-source theorem and finite-word calculus had already received the focused reviews recorded in the preceding work; no broad dependency audit was repeated.

## Quantifiers and numerical budget

In `weak_grushin_explicit_finite_spectator_reserve`, the compact K and open V are selected after the fixed geometry, cutoffs, c, and cutoff coefficient bounds, but before the potential P, finite order m, families G/F, and common budgets K0/W0/H0. The conclusion supplies `tsupport η ⊆ V ⊆ K ⊆ Ω` and `tsupport χ ⊆ K`. No choice of K from later data or word order occurs in the proof.

The potential hypothesis bounds every actual coefficient word `D_a P` of length at most m on that same K. Its empty-word instance supplies the separate bound on P needed by potential reduction. Proper split identities ensure every coefficient and lower solution word used by the commutator is within the given finite order. Lists retain repeated occurrences, with `L_k=2^k−1` proper choices.

The supplied budgets are integrals, not pointwise solution bounds:

`∫_K ‖G_w‖² ≤ W0` and `∫_K ‖F_w‖² ≤ H0` for |w|≤m.

The actual source `R_w=F_w−Commutator_w` is locally L² and satisfies

`∫_K ‖R_w‖² ≤ 2H0+2L_k²K0²W0`.

The one-step potential theorem has budget

`(C0+2C1K0²)∫_K ‖G_w‖² + 2C1∫_K ‖R_w‖²`,

where `C0=4A²+16B(D/2+Q)` and `C1=2M²+8BD`. Substitution gives exactly

`J_k=(C0+2C1K0²)W0+2C1(2H0+2L_k²K0²W0)`.

Both factors 2 in the source contribution are justified: one is from the word-source subtraction and one from removing P in the one-step theorem. Nonnegativity of B, D, Q and the squares gives C0,C1≥0, justifying the substitutions. No separate sign assumption on A or M is needed. No separate H0≥0 premise is needed for these monotone substitutions; the empty-word integral budget already implies it. The condition c>0 justifies the division by 16c.

## Meaning of the witnesses

For each word, the proof obtains a global L² cutoff representative `U=χG_w` almost everywhere, global first derivatives `gy_i`, `gt_j`, and global ordered second Y derivatives `hyy_ij` of U. It then removes χ only inside tests supported on the plateau O where χ=1. The returned relations therefore establish:

- `gy_i = D_yi G_w` in local weak tests on O;
- `gt_j = D_tj G_w` in local weak tests on O;
- globally, `D_yj gy_i = hyy_ij`, which yields local ordered `D_yj D_yi G_w` on O by testing the first identity with `D_yj φ`.

Differentiated compact tests retain their support, so this last composition is valid. The output is not a claim that raw G_w has these global derivatives. O itself is not required to be open by the formal statement: its exact guarantee concerns compact smooth tests supported in O. On an open plateau it has the usual local distributional meaning. Pointwise χ=1 also implies O lies in the support of χ and hence in K⊆Ω.

The norm bounds are respectively `2M²W0+3J_k/4`, `J_k/(16c)`, and `3J_k/2`. None of these newly produced derivative norms is an input or appears as an assumed bound on the right side. The earlier non-explicit reserve preserves the same witness meanings; its forcing norm correctly uses `F_w−fullWordProduct`, the principal source after potential removal.

## Limits and next obligation

Both reserves assume genuine local spectator derivative chains through the finite order m, and only the empty-word PDE. The positive-word equations are derived by the finite calculus. The explicit estimate assumes budgets for the existing G/F words through m; K0, W0, and H0 can depend on m. Thus the common geometry does not by itself provide uniform derivative growth, factorial bounds, or analyticity.

The new spectator witnesses are not explicitly identified with previously named higher words; consistency or extension of word families is a separate step. These statements retain first Y derivatives as well as second Y derivatives, including when instantiated at spectator order eleven, but they alone do not establish a complete isotropic H12 estimate or arbitrary mixed derivative family. No numerical algorithm, novelty, or full Theorem T claim follows from this composition.
