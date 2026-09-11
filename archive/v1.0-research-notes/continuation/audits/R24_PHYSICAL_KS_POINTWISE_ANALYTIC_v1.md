> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual physical KS pointwise factorial bounds and analyticity

The local weak-profile embedding is now instantiated on the physical four-Y,
three-T product. For a scalar Coulomb eigenfunction in the actual H² graph,
take a continuous representative g and a Lipschitz constant L on the physical
ball of radius R. For 0 < ε ≤ min(1,R/4), form the literal normalized difference
`originScaledDifference g ε`, compose with either nuclear KS lift or the pair
KS lift, and apply the proved physical spectator reindexing. Denote the
resulting seven-variable scalar field by f.

The theorem `scalar_coulomb_all_physical_box_pointwise` proves that, for each
real charge Z and energy E, there are C_H,M,A ≥ 1 chosen before the solution,
L,R,ε, chart and unit spectator center t₀, such that f is C∞ and real analytic
on the physical coordinate rectangle centered at (0,t₀) with all seven
half-widths 1/512. Every literal physical coordinate word w, of length k,
satisfies

\[
\|D_w f(y,t)\|\le P Q^k k!,\qquad
Q=6144 C A,
\]

where C=`commonKSBoxFactorialConstant M` and

\[
P=(257/16)^7\,12CA\,(F_0+498\sqrt W)\,Q^{11}\,11!,\quad
F_0=M\|g(0)\|\sqrt{V_{\rm src}},\quad
W=(L^2+\|g(0)\|^2)C_H.
\]

Here V_src is the previously proved `physicalKSUniformSourceVolume`. The
growth rate Q is independent of ε, t₀, derivative order and solution.
The amplitude explicitly retains L and the actual value |g(0)|.

The proof uses one coherent genuine weak jet family supplied by the actual
physical Coulomb PDE theorem. Its weighted local profile on half-width1/256
is bounded by `12CA(F₀+498√W)(3072CA)^r r!`. The actual smooth cutoff has
plateau half-width3/1024 and transition gap1/1024; its closed support is
inside the open half-width1/128 PDE region. The seven-coordinate tensor
box of half-width1/512 lies inside both the plateau and the norm region.
Its exact evaluation constant is (257/16)^7, independent of its center.

The proved R24 weak-to-smooth theorem yields one compatible C∞
representative and the pointwise profile bound with r=k+11. The reserve
is seven tensor derivatives plus four derivatives in the weighted profile
cost. Continuity of the actual base identifies it pointwise with this
representative; no continuous representative of higher weak derivatives
is hypothesized. The inequality

\[
(k+11)!\le 2^{k+11}k!11!
\]

absorbs this fixed reserve and gives the stated P,Q.

On the smaller closed rectangle of half-width1/1024, the literal Fréchet
derivative power series represents f on every ball with the common radius

\[
r_* = \min\{1/1024,\;(7Q)^{-1}\}>0.
\]

This uses the proved coordinate-to-operator norm factor7, the actual block
Euclidean/product norm, and a coordinate triangle-inequality proof of the
interior ball margin. Rectangles are not identified with norm balls.

Evidence: all new theorem statements compile under Lean4.34.0-rc2 and the
pinned Mathlib revision, with strict version8 expanded-statement and
transitive dependency audits. Only `propext`, `Classical.choice` and
`Quot.sound` occur. Development object caches were reused; this checkpoint
does not claim a new isolated dependency rebuild.

Scope: this is a local lifted analytic theorem conditional on an actual
scalar eigenfunction and the explicitly supplied representative/Lipschitz
data. It does not assert existence or uniqueness of that eigenfunction.
The full-spin and ground-state instantiation is separate work. Quantitative
KS descent to physical coordinates, global H² dictionary approximation,
the continuum certificate algorithm and its cost remain further obligations.
No full Theorem T or original rate exponent is asserted here.

Preservation reference: frozen `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. All sources and records above are new
post-freeze continuation files; no frozen or prior PASS artifact was changed.
