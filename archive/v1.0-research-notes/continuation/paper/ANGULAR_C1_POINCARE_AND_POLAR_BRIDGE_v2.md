> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual angular Poincaré foundation for C1 functions

Evidence: fully formal mathematical result in Lean 4.34.0-rc2, compiled against the project's pinned cached dependencies. This record does not claim an isolated source rebuild. All imported continuation proofs retain their successful source bytes.

## Exact result

Let S² be the actual unit sphere in Euclidean R³, with area measure sigma = volume.toSphere and sigma(S²)=4 pi. Let f : R³ -> R be any globally C1 function, with its actual Fréchet derivative. Set

    mean(f) = (1/(4 pi)) integral_S² f(w) d sigma(w),
    t_i f(w) = D f(w) e_i - w_i D f(w) w.

Then

    2 integral_S² (f - mean(f))² d sigma
      <= sum_(i=1)^3 integral_S² (t_i f)² d sigma.

The exact compiled endpoint is
`TheoremT.HydrogenSphereC1Limit.sphere_poincare_contDiff_one`
in `lean/HydrogenSphereC1Limit_v1.lean`, SHA-256
`aa4cefaee858dc35d93de6649168a4304262946657635c4b4fe9432b28b2b271`.
Its only hypothesis is actual global `ContDiff ℝ 1 f`. The companion
`sphere_poincare_contDiff_one_explicit` prints every integral, the mean, and
all actual derivative components directly. There is also a mean-zero corollary.
No Poincaré, spectral decomposition, angular integration by parts, density,
convergence, or extension hypothesis remains.

The final C1 strict audit is
`audits/formal_semantics/20260910T025543_634551Z/receipt.json`.
All 18 declarations in the four limiting modules were fully printed without
ellipses, and their axiom dependencies are only `propext`, `Classical.choice`,
and `Quot.sound`. The polynomial endpoint used in this proof is preserved at
`lean/HydrogenPolynomialSpherePoincare_v1.lean`, SHA-256
`6750bbe3f6330d191bbab23d8f0d515028c998b9e9a709be31ef15feda9a6760`.

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

## Actual C1 limit passage

An independent continuation chain proves C1 polynomial density on the closed
Euclidean unit ball. For every globally C1 real function and every positive
epsilon, one actual polynomial approximates the value and all three actual
first derivatives uniformly. The construction uses tensor Bernstein polynomials,
an exact finite-difference derivative identity, compact parameter estimates,
and affine cube substitution. No mixed derivative hypothesis is used.

Choosing epsilon=1/(n+1) gives one sequence P_n. The actual coordinate formula
for the tangent projection shows that a uniform error delta in all three
ambient derivative components produces an error at most4 delta in each
tangential component on the sphere. Thus P_n and all three tangential
components converge in the supremum norm of actual continuous functions on S².

Integration against the finite actual area measure is proved to be a continuous
linear map on this continuous-function space. Multiplication is continuous, so
squared integrals converge. The spherical mean and centered squared integral
also converge by the same argument. Passing the polynomial inequality to these
four limiting integrals gives the displayed actual C1 inequality. This step
has no remaining integrability or limiting assumption.

The theorem concerns actual ambient global C1 functions restricted to S².
An extension theorem for arbitrary intrinsically defined C1 or H1 data on the
sphere is not claimed. The hypothesis is sufficient for globally smooth
physical test functions and their fixed-radius angular slices.

## Actual physical polar bridge

Separate proved identities now express mass, nuclear attraction, and kinetic
energy of actual smooth compactly supported complex f on R³ as actual polar
integrals. The kinetic identity is

    integral_R³ sum_i |D_i f|²
      = integral_(r>0) [r² integral_S² |Df(rw)w|²
          + sum_i integral_S² |t_i (w -> f(rw))|²] dr.

`TheoremT.Polar.full_kinetic_polar_integral` in
`lean/PolarFullEnergy_v1.lean` proves this equality, and its separated variant
moves the finite sum outside the radial integral. Both use actual C∞ and compact
support hypotheses. No origin exclusion is needed for the kinetic equality.
Separate integrability of every radial and tangential term is proved by the
Euclidean orthogonal decomposition, nonnegative domination by the actual full
kinetic density, the integrable polar product, Fubini, and the explicit radial
weight measure. Its three-module audit is
`audits/formal_semantics/20260910T030347_748802Z/receipt.json` (26 declarations).

The associated `PolarMassCoulomb_v1` and marginal modules prove

    integral_R³ |f|² = integral_(r>0) r² integral_S² |f(rw)|²,
    integral_R³ |f|²/|x| = integral_(r>0) r integral_S² |f(rw)|².

Continuity and compact support suffice for mass. These nuclear statements also
require0 outside the actual closed support; they derive continuity and
integrability of the singular expression rather than assume them.

These angular and polar foundations do not by themselves supply a hydrogen
complement estimate, a rational numerical algorithm, or a bit-complexity theorem.
The active parent program combines them with independently proved radial and
mean-channel facts. Full Theorem T remains unverified.

## Preservation and evidence inventory

The earlier polynomial checkpoint
`logs/angular_foundations_v3/ANGULAR_POLYNOMIAL_CHECKPOINT_v1.json` records 18 final source modules, their hashes, matching successful compile receipts, and strict audits of 112 declarations. The final C1 checkpoint is `logs/angular_density/SPHERE_C1_POINCARE_CHECKPOINT_v1.json`.
The density source review is recorded separately in `logs/angular_foundations_v3/C1_DENSITY_INDEPENDENT_REVIEW_v1.json`; it is a semantic review and is not treated as an additional proof foundation.

The frozen report remains
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`,
tag `theorem-t-proof-freeze-2026-09-09`.
No frozen artifact has been altered. This is a verification contribution, with no claim of mathematical novelty for the classical inequality.
