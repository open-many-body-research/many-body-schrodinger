> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Separation-aware one-electron, two-center lower bounds

This new result strengthens the lower endpoints of the already emitted
molecular stages. It is a paper continuum proof with a directed rational
scalar checker, not a Lean theorem. It changes neither the physical molecule
nor the upper-bound trial space. No reference energy, ground-state attainment,
binding, unique eigenvector or excited-state gap enters the argument.

## Exact model and form inequality

There are exactly two distinct fixed nuclei a_L,a_R in R^3 with charges
z_L,z_R>0, and one electron with both spin components. The electronic
Hamiltonian is -Delta/2-z_L/|x-a_L|-z_R/|x-a_R| on the actual weak H2 domain.
The associated form is on H1(R^3;C^2). The spectral/form identification is the
same explicit paper molecular dependency as in MOLECULAR_COMPUTABILITY_v1.md.
The executable input uses positive rational charges and distinct rational
coordinates, canonicalized exactly as in the existing molecule certificates.

Write c=(a_L+a_R)/2, d=|a_R-a_L|/2>0, and let e be the unit vector from a_L
to a_R. For t=(x-c) dot e /d, the distances satisfy

    |x-a_L| >= d|1+t|,        |x-a_R| >= d|1-t|.

The projection onto this axis is used only in a lower estimate; the electron
still lives in three-dimensional space. No dimensional reduction of the
Hamiltonian is claimed.

Let theta:[-1,1]->[0,pi/2] be continuously differentiable, monotone, with
theta(-1)=0 and theta(1)=pi/2, and extend it constantly outside. Set
chi_L(x)=cos(theta(t)), chi_R(x)=sin(theta(t)). These bounded Lipschitz
multipliers satisfy chi_L^2+chi_R^2=1. Their weak gradients obey

    |grad chi_L|^2+|grad chi_R|^2=theta'(t)^2/d^2

almost everywhere in the interior strip and zero outside. Jumps of the first
derivative at the two strip boundaries are harmless: the proof uses only
H1 forms and bounded first weak derivatives, not second derivatives of chi.

For every f in H1 the weak product rule and chi_L grad chi_L + chi_R grad
chi_R=0 give the exact IMS identity

    q(f)=q(chi_L f)+q(chi_R f)
          -1/2 integral (|grad chi_L|^2+|grad chi_R|^2)|f|^2.

The identity is summed over the two spin components. All Coulomb integrals
exist by translated Hardy and Cauchy-Schwarz, and both localized functions
remain in H1. One may first prove the identity on smooth compact functions
and extend by the H1 multiplication bound and form continuity. No claim that
the Lipschitz-localized function lies in H2 is needed.

The elementary translated hydrogen form inequality is

    1/2 integral |grad g|^2 - z integral |g|^2/|x-a|
       >= -z^2/2 ||g||^2.

It follows by completing the square in grad g + z (x-a)/|x-a| g:
distributional div((x-a)/|x-a|)=2/|x-a|, with no point delta term. Excision
of a radius-r sphere gives a flux error O(r^2) for a smooth test function,
which vanishes; Hardy extends the identity/inequality to H1. Thus this step
does not require identifying an exact hydrogen eigenspace or assuming the
existence of a hydrogen ground state.

Apply that inequality to the left-centered potential on chi_L f and the
right-centered potential on chi_R f, retaining the opposite-center
attractions. With w(t)=sin^2(theta(t)), define, for -1<t<1,

    C(t)=z_L^2(1-w)/2+z_R^2 w/2
          + z_R(1-w)/(d(1-t)) + z_L w/(d(1+t))
          + theta'(t)^2/(2d^2).

Outside the strip use C_left=z_L^2/2+z_R/(2d) and
C_right=z_R^2/2+z_L/(2d). The distance estimates and IMS identity show

    q(f) >= -Cmax ||f||^2,
    Cmax=max(C_left,C_right,sup_(-1<t<1) C(t)).

The apparently singular terms extend continuously to the endpoints because
w(t)=O((1+t)^2) at the left and 1-w(t)=O((1-t)^2) at the right. This proves
the electronic spectral lower bound -Cmax without attainment. Adding the
separately certified nucleus-nucleus constant is permitted afterward.

## A closed-form improvement for the existing H2+ geometry

For equal unit charges at (-1,0,0),(1,0,0), choose theta(t)=pi(t+1)/4. Then

    (1-w)/(1-t)+w/(1+t)
      = [1-t sin(pi t/2)]/(1-t^2) <=1.

For t>=0 this is sine concavity sin(pi t/2)>=t; the negative half follows
by symmetry. The exterior constants are 1. Thus

    E_el >= -3/2-pi^2/32 > -2.

The last strict comparison uses pi^2<16. This already improves the sealed
united-charge lower floor -2. It is an operator/form lower bound using the
actual separated nuclei, not a variational upper bound reinterpreted as a
lower estimate. The directed scalar implementation below allows stronger
partitions without requiring closed-form maximization.

The same linear partition gives a useful general corollary. Put
z_max=max(z_L,z_R). Each opposite-center term is nonnegative, and their
unit-charge sum is at most 1/d by the same sine inequality. The hydrogen
part is at most z_max^2/2. Consequently, for every separation 2d>0,

    E_el >= -z_max^2/2-z_max/d-pi^2/(32d^2).

The explicit normalized hydrogen exponential centered at the stronger
nucleus supplies E_el<=-z_max^2/2, since the additional attraction is
nonpositive. Hence the electronic energy approaches the stronger isolated
hydrogen energy as d tends to infinity, with the explicit one-sided error
at most z_max/d+pi^2/(32d^2). Adding z_L z_R/(2d) yields a corresponding
quantitative statement for the clamped-nucleus total energy. This is a
separation limit, not an excited-state separator or a binding theorem.

## Implemented finite partition family

The exact parameter inputs are rational a,b satisfying |a|+|b|/2<=1/4, with

    theta(t)=pi(t+1)/4+a sin(pi t)+b sin(pi(t+1)/2).

The endpoints are correct, and

    theta'(t)=pi[1/4+a cos(pi t)+(b/2)cos(pi(t+1)/2)] >=0.

Its derivative is bounded above by Ltheta=pi(1/4+|a|+|b|/2). This is a useful
finite search family; neither its optimization nor convergence to the exact
electronic energy is asserted. A rational parameter choice only proposes
a lower-bound certificate, whose complete scalar inequalities are checked.

`two_center_ims_lower_v1.py` divides [-1,1] into J rational cells. A directed
square root of the exact half-distance squared supplies d_lo>0 with d_lo<=d.
Replacing d with d_lo increases every nonnegative inverse-distance and IMS
term, so a scalar upper bound computed this way is conservative. Refinement
of distance arithmetic continues only if its lower endpoint is zero.

For a cell [l,r], monotonicity gives w(t) in [w(l).lo,w(r).hi]. The hydrogen
part is evaluated as z_L^2/2+(z_R^2-z_L^2)w/2, respecting the sign of its
coefficient. The two nonsingular opposite-center terms use their unfavorable
weight and distance endpoints. The cell adjoining -1 instead uses

    w(t)/(1+t) <= Ltheta^2(1+t) <= Ltheta^2(1+r),

and the cell adjoining 1 uses the analogous
(1-w(t))/(1-t)<=Ltheta^2(1-l). These follow from sin u<=u and the global
derivative bound; they do not divide an interval by zero or discard a
singular endpoint. They also apply if a single cell spans the whole strip.

Cosine monotonicity/evenness on [-1,1] encloses theta' on each cell; squaring
its nonnegative upper bound gives the IMS term. The maximum of all rational
cell upper bounds and both exterior constants is an explicit upper bound
for Cmax. Outward rounding of its negative supplies the emitted lower energy.
Every cell and each component upper bound is retained in the certificate.

The sine evaluations at rational multiples of pi reuse the sealed rational
Machin/Taylor kernel. The additional `sin_small` handles a rational interval
inside [-2,2] by its full Taylor polynomial plus a symmetric Lagrange remainder.
It is used on the narrowly enclosed endpoint theta values. Dyadic rounding
before the nested Taylor call limits operand growth without assuming
floating-point accuracy. Intersections with [0,pi/2] and[0,1] use the proved
theta and sine ranges. The scalar checker contains no reference digits.

## Certificates and evidence boundary

`bound` emits the physical input, partition parameters, rational half-distance
interval, all cell inequalities, exterior constants, final lower endpoint
and source hashes. `check` recomputes those fields. `combine` checks the lower
certificate and, by default and in the CLI, fully replays the sealed molecular
stage before intersecting its old energy interval with the new lower bound.
The physical nucleus lists and electron counts must agree exactly. The
strengthened certificate checker repeats both complete computations.

The finite parameter comparisons are not an optimization theorem. The scalar
grid has no hidden continuum-energy oracle: all accepted lower endpoints
follow from the inequalities above for any permitted finite grid/precision.
Finite arithmetic success and independent review do not constitute Lean
verification of IMS, hydrogen square completion, molecular form realization,
or the Python implementation. Those formal bridges remain separate.

The source-only replay, exact tests, concrete new intervals, timing, and the
environmental import incident are recorded in TWO_CENTER_IMS_EXECUTION_v1.md.
This work preserves the molecular seal
MOLECULAR_SEALED_MANIFEST_v1.json, SHA-256
1d37b073eb2c18f4a2f4bd9735fe7b2272b705da12ed4c0f0fef9417ce2ef3a0.
The frozen baseline remains commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660,
tag theorem-t-proof-freeze-2026-09-09, with no modified historical artifact.
