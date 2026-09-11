> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Formal local KS analyticity for an actual two-electron ground state

Evidence: kernel-checked mathematical theorem, with pinned dependency caches
reused. This is a local lifted regularity result within Rung 2. It is not the
global approximation theorem or an energy computation algorithm.

Fix real Z>0 with 32<9Z², in particular any real Z≥2. The model is

H = −(Δ₁+Δ₂)/2 − Z/|x₁| − Z/|x₂| + 1/|x₁−x₂|,

on the actual weak H² domain in the full fermionic spin-space, where spatial
and spin coordinates are permuted simultaneously. The previously established
operator foundation and ground-branch theorem supply a normalized ground
vector g and identify its eigenvalue E with the bottom of the actual continuum
spectrum. The new theorem retains that domain, spectrum membership, lower
spectral bound, normalization and normalized symmetric spatial singlet link.

There is one genuine full-spin representative u, locally Lipschitz in every
spin component, one common Lipschitz constant L on a ball of radius R>0, and
finite constants C_H,M,A≥1. Let

v_(ε,σ)(x) = [u_σ(εx)−u_σ(0)]/ε,

for 0<ε≤min(1,R/4). Pull v back through either nuclear KS lift or through the
electron-pair KS lift, and use the proved spectator-coordinate isometry into
Y∈R⁴,T∈R³. For every unit spectator center t₀, the resulting actual function f
is C∞ and real analytic on the coordinate rectangle centered at (0,t₀) with
every half-width equal to 1/512. For every ordered word w in the seven physical
coordinate directions, of length k,

‖D_w f(Y,T)‖ ≤ P Q^k k!,

throughout that rectangle. Write C=commonKSBoxFactorialConstant(M). The bound
uses the explicit expressions

Q = 6144 C A,

P = (257/16)^7 · 12 C A · (F₀+498√W) · Q^11 · 11!,

F₀ = M (Σ_σ |u_σ(0)|²)^(1/2) √V,

W = [L²+Σ_σ |u_σ(0)|²] C_H.

Here V is the actual fixed finite volume `physicalKSUniformSourceVolume`.
C_H,M,A are chosen before the input eigenvector in the generic theorem for
fixed Z,E. The representative, L,R,F₀,W are chosen before spin, scale, chart,
unit center and derivative order. They are finite quantities, not evaluated
numerical parameters or an executable selection procedure.

The separately proved common-radius lemma applies directly to this pointwise
data: at each point of the smaller closed rectangle of half-width 1/1024,
the literal real Fréchet derivative Taylor series represents f on the ball
of radius min(1/1024,(7Q)⁻¹). The block Euclidean norms and their maximum product
norm remain the actual norms; coordinate rectangles are never identified
with Euclidean balls. This result does not assert a complex polydisc descent
to the three physical distance variables.

The proof starts with the original weak Coulomb graph. The true scaled KS
equations have principal constants c=4 in the nuclear charts and c=1 in the
pair chart. Known coefficient and source estimates, actual H¹² initialization,
and the original weak PDE produce one coherent all-order weak derivative
family. Its actual weighted L² profiles obey a fixed-gap factorial recurrence.
The exact seven-coordinate tensor estimate constructs compatible smooth
representatives, identifies the original continuous base, and uses eleven
extra profile orders. Absorbing that fixed reserve gives the displayed P,Q;
the actual Taylor remainder theorem then gives real analyticity. No solution
smoothness, higher-derivative bound, recurrence or analytic conclusion is an
input assumption.

The ground theorem is `twoElectron_physical_ground_pointwise` in
`lean/TwoElectronGroundPhysicalPointwise_v1.lean`. Its generic full-spin input
theorem is `coulomb_spin_physical_pointwise_representative`. The final checkpoint
is `audits/COULOMB_SPIN_GROUND_PHYSICAL_POINTWISE_CHECKPOINT_v1.json`, SHA-256
`94e82e50419c8febe9e7c7e36978f0651e0e4a16a3643c5d13a453a9a310dd88`.
It links source/object hashes, expanded statements, axiom reports and focused
independent reviews. The proof closures use only `propext`, `Classical.choice`
and `Quot.sound`. These new modules are outside isolated source rebuild v20.

Quantitative KS descent, compatible collision and coordinate-boundary germs,
the exterior uniform estimates, the exact dyadic dictionary's global H²
approximation, physical moments, the rational solver, termination and binary
cost remain separate obligations. Full Theorem T and the original exponents
2256 and 1/16 remain formally unverified. No novelty claim is made here.

Frozen provenance: `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. All sources described here are new
continuation files; frozen and prior successful artifacts remain unchanged.
