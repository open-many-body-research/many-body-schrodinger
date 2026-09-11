> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual mean-zero angular sector comparison

Let sigma be actual Euclidean sphere area measure on S², of mass4 pi. For an
actual complex-valued function g on R³ set

    Q_Z(g) = (1/2) integral_R³ sum_i |D_i g|²
             - Z integral_R³ |g(x)|²/|x|.

The continuation now proves the following statement in Lean: if g is globally
C∞, compactly supported, its closed support excludes0, and

    integral_S² g(rw) d sigma(w) = 0  for every r>0,

then, for every real Z,

    Q_Z(g) >= -(Z²/8) integral_R³ |g|².

The exact theorem is
`TheoremT.Polar.mean_zero_sector_energy_lower` in
`lean/PolarMeanZeroSector_v1.lean`. There is no assumed angular inequality,
radial comparison, Fubini identity, or integrability conclusion in its hypotheses.
The derivatives and integrals are actual Euclidean Fréchet derivatives and
Lebesgue/sphere integrals.

A second endpoint applies this directly to the physical fluctuation of any
punctured smooth compact f:

    m_f(r) = (1/(4 pi)) integral_S² f(rw) d sigma(w),
    g_f(x) = f(x) - m_f(|x|).

`TheoremT.Polar.physicalFluctuation_energy_lower` assumes only that actual f is
C∞, has compact support, and has0 outside its closed support. The imported
source proves that g_f has all these properties and that its actual spherical
mean vanishes. In particular, no spectral projection or ground-state-orthogonality
condition is silently substituted for zero spherical mean.

The final module SHA-256 is
`511890f79c2658335f264674270fa92695346769c7b151662c036a467e769d7e`.

## Proof

For each nonzero direction w, the actual function u_w(r)=r f(rw) on r>0,
extended by0 on the negative half-line, is proved to belong to the actual
half-line test domain. Its value, derivative and quotient are identified almost
everywhere. The proved half-line kinetic cancellation gives

    ||u_w||² = integral_(r>0) r² |f(rw)|²,
    ||u_w'||² = integral_(r>0) r² |Df(rw)w|²,
    ||u_w/r||² = integral_(r>0) |f(rw)|².

The nuclear moment is integral r|f(rw)|². The actual ell=1 centrifugal bound
therefore gives, on each ray,

    -(Z²/8) integral r²|f|²
       <= (1/2) integral r²|Df w|² - Z integral r|f|² + integral |f|².

All four directional marginals are proved integrable in w. The mass and nuclear
moments use the actual polar measure-preserving map. The radial kinetic marginal
uses domination by full kinetic energy, and the inverse-square marginal uses
actual continuity and compact support away from0. Integrating the ray inequality
and applying proved Fubini yields

    -(Z²/8)||f||² <= (1/2) R(f) - Z V(f) + I(f),

where R is the actual radial kinetic integral, V is the nuclear moment, and
I=integral_R³ |f(x)|²/|x|².

For a zero-mean angular slice, the actual complex sphere Poincaré inequality
with constant2 gives

    2 integral_S² |f(rw)|² <= sum_i integral_S² |t_i (y -> f(ry))(w)|².

Both sides are integrable over positive r. Thus I(f)<=A(f)/2, where A is the
actual tangential kinetic integral. The actual full kinetic identity K=R+A
proves the displayed form bound. Every limiting, polar, support, and integrability
premise in this composition has been discharged.

## Evidence and remaining scope

This is a kernel-compiled mathematical form comparison using the project's
pinned Lean4.34.0-rc2 environment and existing pinned dependency objects.
Only `propext`, `Classical.choice`, and `Quot.sound` are acceptable axioms in the
strict audits. Cache use is disclosed; the parent reproduction program owns the
isolated source rebuild supplement.

The intermediate `PolarCentrifugalSector_v1` is deliberately retained as a
conditional composition theorem with an explicit actual angular inequality.
`PolarMeanZeroSector_v1` discharges that premise. They are distinct evidence
categories; the conditional file is not passed off as the completed endpoint.

Zero spherical mean excludes the entire radial channel. The full complement of
the hydrogen ground vector also contains radial excited directions, so this
result alone is not the full ground-orthogonal complement theorem. That remaining
radial/mean-channel comparison and its composition belong to the active parent
program. A weak-H1 extension of the final full comparison is also separate.
Full Theorem T is not claimed here, and no mathematical novelty is asserted for
the classical sector inequality.

The frozen baseline is
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`,
tag `theorem-t-proof-freeze-2026-09-09`. Frozen and successful sources remain
unchanged; this manuscript and every new proof use new continuation paths.
