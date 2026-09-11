> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact weak Grushin outer maximal estimate

Let P_c=-Δ_Y-c|y|²Δ_T on the actual product Lebesgue space R⁴×R³, with c>0. Let f,h be complex L2 functions. Assume actual global first and ordered second weak L2 witnesses d(v),e(v,w) for f, and the genuine compact-real-test equation P_c f=h. Suppose f vanishes almost everywhere outside a compact K, and for one Y coordinate i0,

|y_i0|≤R on K, R>0; |y|≤S on K, S≥1.

The compiled theorem constructs L2 representatives D_{αβ}=D_Y^α D_T^β f through total order two, with D_00=f, original K support, both compact-test integrabilities and the exact canonical-word distribution identity with sign (-1)^(|α|+|β|). It also constructs every monomial-weighted representative W_{αβγ}=y^γ D_{αβ} for the fixed index set

M={(α,β,γ): |α|+|β|≤2, |γ|≤2, |α|+2|β|≤|γ|+2}.

This set has exactly 498 indices. Its actual sum of L2 norms satisfies

Σ_M ||W_{αβγ}||₂ ≤ 498 S² (4R²+2R+2+2/c) ||h||₂.

The underlying radius-free weak estimates include every individual |y|²-weighted spectator Hessian component. Genuine weak derivatives preserve the original closed support by compact-test uniqueness. Approximation uses the existing compact H2 density theorem with one possibly larger support L, but L is used only in continuous-weight L2 convergence. The radius R enters only after the limit via the actual support of f. The energy/Poincare argument gives the zeroth and first-Y bounds; positive scalar inequalities supply the common coefficient. The canonical natural jet is identified with all six low-order component cases by smooth approximation and uniqueness of L2 limits. The outer norm is independent of choices of representatives and transfers across AE-equal derivative fields.

This is a formal compact weak H2 implication with explicit derivative witnesses, not a proof of all-order smoothness or a factorial recurrence. It supplies a maximal-estimate step for the ongoing R02 argument. Weighted TT control does not imply unweighted TT control at y=0. Constructed Lp objects and mathematical existence do not constitute an executable numerical procedure. No novelty claim is made.

Four modules in this final semantic/synthesis unit contain 13 declarations and pass strict v7 audits of exact expanded statements, complete axiom dependencies and immutable source/object hashes. Only propext, Classical.choice and Quot.sound occur. The dependency checkpoints record the previously sealed weak radial, energy, slab, canonical-jet and finite-index assembly units. Lean 4.34.0-rc2 reused pinned library and continuation objects; no isolated source rebuild was attempted in this bounded unit.

Development failures were elaboration-only (namespace/import resolution and a recursion-depth setting for the large finite index type); all failed logs remain. A separately passed identification v1 duplicated the canonical support symbol. Both old byte streams are preserved; integration uses the new identification v2, and the final combined imports compile and audit successfully.

Next: transfer the bound to the independently chosen raw derivative family via actual compact-test uniqueness, then use it with the differentiated PDE and cutoff commutator in the factorial recurrence. Full Theorem T remains outside this result.
