> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual angular Poincaré foundation, polynomial checkpoint

Evidence: fully formal mathematical result in Lean 4.34.0-rc2, compiled against the project's pinned cached dependencies. This record does not claim an isolated source rebuild. All imported continuation proofs retain their successful source bytes.

## Exact result

Let S² be the actual unit sphere in Euclidean R³, with area measure sigma = volume.toSphere and sigma(S²)=4 pi. Let P be any real polynomial in three variables, evaluated at actual Euclidean coordinates. Set

    mean(P) = (1/(4 pi)) integral_S² P(w) d sigma(w),
    t_i P(w) = D P(w) e_i - w_i D P(w) w.

Then

    2 integral_S² (P - mean(P))² d sigma
      <= sum_(i=1)^3 integral_S² (t_i P)² d sigma.

The exact compiled endpoint is
`TheoremT.HydrogenPolynomial.polynomial_sphere_poincare`
in `lean/HydrogenPolynomialSpherePoincare_v1.lean`, SHA-256
`6750bbe3f6330d191bbab23d8f0d515028c998b9e9a709be31ef15feda9a6760`.
Its only input is the actual real multivariate polynomial. It has no Poincaré, spectral decomposition, angular integration by parts, or approximation hypothesis.

The final strict audit is
`audits/formal_semantics/20260910T025145_790907Z/receipt.json`.
All four final-module declarations were fully printed without ellipses, and their axiom dependencies are only `propext`, `Classical.choice`, and `Quot.sound`.

## Proof and the analytic bridges actually discharged

For a homogeneous harmonic polynomial H of degree m, define its degree-zero extension off the origin by

    Y_H(x) = |x|^(-m) H(x).

The definitions use actual Euclidean polynomial evaluation, Fréchet derivatives, the squared Euclidean norm, and real powers. The symbolic polynomial derivative and Laplacian are first proved equal to the corresponding actual Euclidean derivatives. Direct calculus then gives

    D Y_H(x) x = 0,
    Delta Y_H(x) = -m(m+1) |x|^(-2) Y_H(x),  x != 0.

No angular differential operator is introduced by a spectral definition. No smoothness at the origin is assumed.

Take the concrete nonnegative smooth bump eta centered at 1, with inner radius 1/4 and outer radius 1/2. The Euclidean cutoff chi(x)=eta(|x|²) is smooth, compactly supported, and has the origin outside its closed support. Every cutoff product used in the proof is globally smooth and integrable; these facts are derived from smoothness away from zero and the support exclusion. The radial constant

    C = integral_(r>0) eta(r²) dr

is proved strictly positive: the explicit profile equals 1 for r in (1,17/16).

Actual Euclidean integration by parts with this cutoff gives

    sum_i integral_R³ chi D_i Y_Q D_i Y_H
      = m(m+1) integral_R³ chi |x|^(-2) Y_Q Y_H.

The derivative-of-cutoff term vanishes because the cutoff is radial and D Y_H(x) x=0. Actual nonradial polar integration, together with the degree-zero scaling of Y and degree-minus-one scaling of its derivative, identifies both sides as C times their corresponding sphere integrals. Cancellation of the proved positive C gives

    E(Y_Q,Y_H) = m(m+1) I(Y_Q,Y_H),

where I is the actual sphere integral of the product and E is the sum of the three actual derivative-product integrals. Symmetry implies orthogonality of different harmonic degrees. Degree zero is the constant component; positive degrees have integral zero.

Algebraic harmonic decomposition is independently proved for actual finite polynomials, then grouped by degree. On the actual Euclidean sphere, every P is a finite sum of homogeneous harmonic restrictions. The sum has diagonal norm and energy:

    I(sum_m Y_m, sum_m Y_m) = sum_m I(Y_m,Y_m),
    E(sum_m Y_m, sum_m Y_m) = sum_m m(m+1) I(Y_m,Y_m).

Subtracting the actual mean removes precisely degree zero. For every positive integer m, m(m+1)>=2, and each diagonal norm integral is nonnegative. This proves the centered finite harmonic inequality.

A trace identity alone would not justify an ambient derivative identity. The proof instead extends the trace equality to a genuine neighborhood off zero through the map x -> x/|x|. At a unit vector w, the derivative of this map sends v to v-<w,v>w. The actual derivative of the polynomial retraction therefore has coordinates t_i P(w). Equality of the two actual functions on a neighborhood gives equality of their actual derivatives and transfers the finite harmonic energy to the stated polynomial tangential energy.

## Approximation frontier at this checkpoint

An independent continuation chain has compiled actual C1 polynomial density on the closed Euclidean unit ball. For every globally C1 real function and every positive epsilon, one actual polynomial approximates the value and all three actual first derivatives uniformly. Its construction uses tensor Bernstein polynomials, an exact finite-difference derivative identity, compact parameter estimates, and affine cube substitution. No mixed derivative hypothesis is used.

At this checkpoint the passage from that approximation to the sphere inequality for all actual C1 functions remains the active obligation. Uniform approximation must be passed through the actual mean, centered squared integral, and all three tangential squared integrals. Polynomial density alone is not recorded as a completed smooth-function inequality.

Neither the angular theorem nor polynomial density supplies a hydrogen complement estimate, an effective rational approximation algorithm, or a bit-complexity theorem. Arbitrary real polynomial coefficients and noncomputable existence of a convergence index do not count as a numerical implementation. Full Theorem T remains unverified.

## Preservation and evidence inventory

`logs/angular_foundations_v3/ANGULAR_POLYNOMIAL_CHECKPOINT_v1.json` records 18 final source modules, their hashes, matching successful compile receipts, and strict audits of 112 declarations. The density source review is recorded separately in `logs/angular_foundations_v3/C1_DENSITY_INDEPENDENT_REVIEW_v1.json`; it is a semantic review and is not treated as an additional proof foundation.

The frozen report remains
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`,
tag `theorem-t-proof-freeze-2026-09-09`.
No frozen artifact has been altered. This is a verification contribution, with no claim of mathematical novelty for the classical inequality.
