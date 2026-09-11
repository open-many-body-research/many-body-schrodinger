> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Actual Coulomb ground states: spectral separation, symmetry and H² decay

This continuation proves statements about the continuum operator
\[
H_{N,Z}=-\tfrac12\sum_{i=1}^N\Delta_i-Z\sum_{i=1}^N|x_i|^{-1}
              +\sum_{i<j}|x_i-x_j|^{-1}.
\]
The full spin space has simultaneous spatial and spin antisymmetry. Its
operator domain is the actual weak Sobolev H² domain intersected with that
fermionic space. The prior formal foundation establishes dense definition,
self-adjointness on this exact domain, semiboundedness and equality between
the variational and actual spectral infima for every finite N and real Z.

## Exact two-electron result

For every real Z ≥ 2, the full fermionic spectral bottom E_Z is attained.
It has a one-dimensional complex eigenspace and satisfies
\[
 E_Z\le-9Z^2/14,\qquad
 \sigma(H_{2,Z})\setminus\{E_Z\}\subset[E_Z+Z^2/56,\infty).
\]
Its spin state is a singlet. A normalized spatial eigenfunction u can be
chosen real almost everywhere, symmetric under electron exchange and fixed
in L² by every simultaneous orthogonal transformation of the two positions.
The invariance is a statement about the actual L² class; a canonical
pointwise Lipschitz representative remains a separate formal obligation.

Let ρ(x) = (|x₁|²+|x₂|²)¹ᐟ². For every a ≥ 0 with a² < Z²/112,
\[
 e^{a\rho}u,\quad e^{a\rho}\partial_k u,\quad
 e^{a\rho}\partial_l\partial_k u\ \in L^2,
\]
for every ordered pair of actual weak coordinate derivatives. Consequently
there exists a finite C, depending on u, Z and a, such that
\[
 \left(\|u\|_{L^2(\rho\ge r)}^2+
 \sum_k\|\partial_k u\|_{L^2(\rho\ge r)}^2+
 \sum_{k,l}\|\partial_l\partial_k u\|_{L^2(\rho\ge r)}^2\right)^{1/2}
 \le C e^{-ar}\qquad(r\in\mathbb R).
\]
The corresponding spin-summed result holds for every actual full fermionic
ground eigenvector, with all its actual weak derivative components.

For S = |x₁|+|x₂|, taking a = Z/16 gives the physical tail
\[
 \|u\|_{H^2_*(S\ge r)}\le C\exp\left(-\frac{Zr}{16\sqrt2}\right).
\]
The H²-star norm includes the entire ordered Hessian. The √2 loss comes from
S ≤ √2 ρ. Derivative transfer itself preserves the Euclidean exponent.
The theorem supplies a finite prefactor; no explicit upper bound or
algorithm for computing that prefactor is claimed.

## Shared derivative-transfer theorem

For any finite N, real Z,E and an actual scalar H² Coulomb eigenfunction f,
the premise e^{a|x|}f ∈ L², a ≥ 0, implies the same weighted L² membership
for every first and ordered second weak derivative, and the corresponding
H² tail bound. The full finite spin sum is also formalized. No binding,
attainment, spectral isolation or uniqueness is needed for this implication.
It does not assert that arbitrary atoms bind or that arbitrary eigenfunctions
have positive exponential decay. The explicit decay premise is discharged
for the two-electron ground state in the charge range above.

## Proof structure

The proved hydrogen rank-one comparison and an actual H² hydrogen-product
trial give ground-state attainment and spectral separation. Actual Coulomb
graph covariance, overlap uniqueness, conjugation and spin decomposition
give the stated symmetry and realness properties.

For Z ≥ 2, the scalar H¹ rank-one comparison gives a finite R > 0 such that
every actual H¹ vector v vanishing on the radius-R ball satisfies
\[
 q(v)-E_Z\|v\|^2\ge (Z^2/112)\|v\|^2.
\]
The radius follows from L² localization of the literal hydrogen product.
It is existential. Neither a decay premise nor an ionization threshold is
used as a substitute for this exterior form bound.

Actual weak multiplier calculus proves the weighted eigenfunction identity
\[
 q(\chi f)-E\|\chi f\|^2=\tfrac12\sum_k\|(\partial_k\chi)f\|^2
\]
for bounded smooth real weights with bounded first derivatives. In
particular, no fourth derivative or domain-of-H² premise is introduced.
With ρ₁(x) = √(1+|x|²), the smooth saturations
\[
 w_L(x)=\frac{L e^{a\rho_1(x)}}{L+e^{a\rho_1(x)}}
\]
satisfy w_L ≤ L, w_L ≤ e^{aρ₁}, and
\[
 \sum_k|\partial_k w_L|^2\le a^2w_L^2,\qquad
 |\partial_l\partial_k w_L|\le(a^2+2a)w_L.
\]
An exterior cutoff and the form bound yield a uniform weighted L² estimate.
A countable intersection of almost-everywhere representative identities
licenses the Fatou passage L = n+1 → ∞. The interior contribution is restored
by a compactly supported multiplier.

For derivative transfer, Hardy's actual H¹ multiplication bound and the
weighted identity control the first derivatives. They also control the
weighted Coulomb potential and the weighted Laplacian through the actual
eigen-equation. Fourier covariance gives
\(\|\partial_l\partial_k g\|_2\le\|\Delta g\|_2\).
The weak product rule and the uniform second-derivative bound on w_L then
control every weighted mixed derivative. A second Fatou passage gives the
claimed same-exponent transfer. All finite spin and coordinate sums occur
explicitly in the formal statements.

## Evidence and remaining frontier

The source modules and expanded-statement/axiom receipts are recorded in
`audits/PHYSICAL_GROUND_ROTATION_CHECKPOINT_v1.json`,
`audits/EXTERIOR_WEIGHTED_FORM_CHECKPOINT_v1.json`,
`audits/PHYSICAL_EXPONENTIAL_DECAY_CHECKPOINT_v1.json`,
`audits/PHYSICAL_FIRST_DERIVATIVE_DECAY_CHECKPOINT_v1.json`, and the subsequent
H² decay checkpoint. These are Lean kernel proofs under the pinned
Lean 4.34.0-rc2 and Mathlib environment. The audited dependencies use only
propext, Classical.choice and Quot.sound. Development builds reuse pinned
dependency objects. The later decay modules are outside the currently
running 392-source Colab rebuild; its unfinished status must not be reported
as independent source reproduction of this result. The compiler and core
binaries themselves have not been bootstrapped from source.

This manuscript makes no novelty claim for the underlying physical
regularity and decay theorems. The formalization is the demonstrated result.
Global boundedness, local Lipschitz regularity through collisions, the weak
KS analytic chain, unchanged-dictionary approximation, exact moments,
an executable two-electron interval producer, termination and bit complexity
remain distinct obligations. Their inherited paper arguments have not become
Lean proofs through this composition. Full Theorem T remains unverified.

The frozen reference is `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`,
SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`,
tag `theorem-t-proof-freeze-2026-09-09`. Frozen and successful earlier
artifacts are preserved unchanged. The original trial dictionary is unchanged.
