> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual two-electron ground-state analytic distance decomposition

This note records a formal local result in the Rung 2 dependency chain.
It does not assert full Theorem T, a global approximation theorem, or an
executable certified energy algorithm. No novelty claim is made.

## Exact objects and hypotheses

For `Z > 0` and `32 < 9 Z²`, the theorem
`twoElectron_physical_ground_analytic_descent` in
`lean/TwoElectronGroundPhysicalAnalyticDescent_v1.lean` constructs a
normalized ground vector of the existing two-electron Coulomb operator on
the actual fermionic weak H² domain. The operator is the continuum
Hamiltonian with kinetic coefficient −1/2, attractive nuclear terms,
and repulsive electron–electron interaction. Its energy is proved to be
the bottom of the actual continuum spectrum. The original spatial H²
singlet and simultaneous space/spin permutation conclusions are retained.

There is one full-spin representative `u`, equal almost everywhere to that
vector, and common constants `C_H, M, A ≥ 1`. The representative has a
positive local Lipschitz radius `R`. For each spin component σ and every

\[
0<\varepsilon\leq\min(1,R/4),
\qquad
v_{\varepsilon,\sigma}(q)
=\varepsilon^{-1}\bigl(u_\sigma(\varepsilon q)-u_\sigma(0)\bigr),
\]

the following conclusions hold with the same `M,A`. No derivative of `u`
at the origin is assumed by this definition.

## Coordinates, radii, and statement

In a nuclear chart, `X` is the position of the selected electron and `T`
is the position of the other electron. Either electron can be selected.
In the pair chart, the two positions are `T+X/2` and `T−X/2`, so `X` is
their difference and `T` their midpoint. Denote either actual coordinate
map by `C(X,T)`.

Fix any real `t0` with Euclidean norm one. Put

\[
S=7\,\mathrm{physicalKSPointwiseRate}(M,A),\qquad
D=32S^2,\qquad
r=\min(1/1024,S^{-1}),\qquad
\rho=\min(r^2,D^{-1}).
\]

All these radii are positive. The literal functions `A_desc` and `B_desc`
constructed from the actual derivative Taylor coefficients are jointly
complex analytic on

\[
D\|X\|_\infty<1,\qquad S\|T\|_\infty<1.
\]

For every real physical `X,T` satisfying
`‖X‖₂ < ρ` and `‖T‖₂ < r`, the formal physical-coordinate identity is

\[
v_{\varepsilon,\sigma}\bigl(C(X,t_0+T)\bigr)
= A_{\rm desc}(X,T)+\|X\|_2 B_{\rm desc}(X,T).
\]

The collision point `X=0` is included. Here `T` on the right is an
increment; the center `t0` is added exactly once on the left. The real
Euclidean norms and the complex coordinate sup norms are distinct.
The proofs connect them by coordinate inequalities.

## What the proof establishes

The KS pullback has actual factorial derivative bounds and a convergent
joint seven-coordinate Taylor series. Spectator coefficient extraction
at total order `j+|γ|` gives a four-variable homogeneous polynomial of Y
degree `j`, retaining its original coefficients. Actual circle invariance
forces balanced spinor support and vanishing of odd **Y** degree. Odd
total Taylor degrees are retained when the spectator degree is odd.

The extracted double series is proved absolutely summable and is then
regrouped into the original joint Taylor series. This establishes its
sum as the same physical function. Finite polynomial KS descent produces
the literal A and B coefficients; the B series uses the proved successor
shift and zero initial slice. The resulting double sums are jointly
analytic with the two stated rates and satisfy the actual pullback
identity with factor `‖Y‖²`.

The already proved surjectivity of the actual KS map supplies a preimage
for every physical `X` with `‖Y‖²=‖X‖`. This proves the displayed physical
identity on the quantitative neighborhood. No continuous or analytic
inverse section of the KS map is assumed.

## Evidence and remaining boundary

The assembled full-spin and ground result is sealed in
`audits/COULOMB_SPIN_GROUND_ANALYTIC_DESCENT_CHECKPOINT_v1.json`
(SHA-256 `6ee0000b29e3bf1c1508d13f054d859c7b006d3b6df7b252f160b99d59b08d02`).
The physical transfer is sealed in
`audits/PHYSICAL_KS_ANALYTIC_DESCENT_SURJECTIVITY_CHECKPOINT_v1.json`
(SHA-256 `327568ba837f1ef07fa0e75809754ec26f51839dc619afc340d07b39f8cb2a7a`).
The records bind exact sources, expanded-statement/axiom audits and
independent reviews. Only `propext`, `Classical.choice`, and `Quot.sound`
occur in these final axiom reports. Builds reuse pinned development
objects and are outside the earlier isolated source-rebuild checkpoint v20.

The constants are not numerically evaluated. The coefficient and series
definitions are mathematical, noncomputable objects. Mixed derivative
estimates, compatible germs, complete collision and exterior coverage,
global H² approximation by the exact dyadic dictionary, rational solver
correctness, termination and operational bit cost require their own
verified results. The original exponents 2256 and 1/16 remain unverified.

## Frozen provenance

Frozen target: `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`;
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. This is a new continuation note;
frozen and prior successful artifacts are preserved.
