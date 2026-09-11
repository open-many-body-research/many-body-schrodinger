> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Physical hydrogen complement from a punctured core and one half-line factorization

Status: **unsealed paper proof draft**. The angular proof and three-dimensional assembly below are given explicitly. The separately developed half-line lemma must be bound to its stable reviewed source before this draft is sealed. This file does not assert a Lean proof of the physical complement bound.

Let Z>0 and let

    q_Z[f] = (1/2) ||grad f||_2^2 - Z integral |f(x)|^2/|x| dx,
    phi_Z(x) = sqrt(Z^3/pi) exp(-Z|x|).

Here f belongs to the actual scalar weak H1(R^3;C), with Euclidean Lebesgue measure and the same kinetic normalization as the current formal continuum model. Hardy's inequality makes the Coulomb integral finite. The ground profile phi_Z has norm one; the actual weak H2 graph and its energy -Z^2/2 are already formally proved in the hydrogen branch.

The target paper conclusion is the complete scalar form comparison

    q_Z[f] >= -(Z^2/8) ||f||_2^2
               -(3 Z^2/8) |<phi_Z,f>|^2.                      (P1)

Thus the scalar ground-orthogonal form is bounded below by -Z^2/8. The corresponding energy difference is 3Z^2/8. No scalar gap may be inferred solely from the previously constructed ground eigenfunction; the argument below supplies the additional comparison.

## 1. A legitimate core avoiding the origin

Begin with f in C_c^infinity(R^3 minus {0}). This class is dense in actual H1(R^3). To see the assertion with no point-removal assumption, first approximate an arbitrary H1 function by ordinary compact smooth functions in the complete first-derivative graph norm. This density is already established in the current formal branch.

For a fixed compact smooth v, choose a smooth radial cutoff eta_epsilon equal to zero on the ball of radius epsilon, one outside the ball of radius 2epsilon, with |grad eta_epsilon| <= C/epsilon. The function v eta_epsilon is compact smooth and avoids the origin. With v and grad v bounded, the squared L2 error is O(epsilon^3). The squared derivative error from (1-eta_epsilon)grad v is O(epsilon^3), and the error from v grad eta_epsilon is O(epsilon), since its support has volume O(epsilon^3). All implied constants here depend only on the fixed v and the fixed cutoff. First choosing v, then epsilon, gives the claimed H1 density. This proves the required capacity fact rather than assuming that a null point may be removed from a Sobolev core.

The inequality will be proved for every element of this core, without imposing exact orthogonality on its approximants. Its global rank-one form (P1) will then pass to H1 by continuity.

## 2. Sharp angular inequality without a supplied spherical spectrum

Let dnu be the uniform probability area measure on the unit sphere S^2. For every smooth complex function a on S^2, write abar=integral a dnu. Then

    integral |grad_S a|^2 dnu >= 2 integral |a-abar|^2 dnu.     (P2)

Here grad_S is the tangential gradient for the unit-radius Euclidean sphere. The radius-one convention is essential to the number 2.

One direct derivation of (P2) uses only polynomials and Euclidean integration by parts. Every homogeneous polynomial P of degree k in three coordinates admits a decomposition into terms |x|^(2j) H_(k-2j)(x), where each H_m is homogeneous harmonic of degree m. An induction supplies the decomposition: decompose Delta P at degree k-2, and use

    Delta(|x|^(2j) H_m) = 2j(2m+2j+1) |x|^(2j-2) H_m        (P3)

for j>=1 to find a homogeneous polynomial Q with Delta Q=Delta P. All the coefficients divided by in this construction are strictly positive. Then P-Q is harmonic. Formula (P3) follows from the product rule, Euler's identity x dot grad H_m=m H_m, and Delta H_m=0. Degrees zero and one begin the induction.

For Y_m=H_m restricted to the sphere, extend Y_m homogeneously with degree zero on R^3 minus {0}. Direct Euclidean differentiation gives

    x dot grad Y_m = 0,
    Delta Y_m = -m(m+1) |x|^(-2) Y_m.                         (P4)

To justify the angular integration identity, choose a nonnegative smooth radial chi supported in an annulus, with integral chi(r) dr>0. Euclidean integration by parts for chi times the homogeneous extensions gives

    integral chi grad conjugate(Y_l) dot grad Y_m dx
       = m(m+1) integral chi |x|^(-2) conjugate(Y_l) Y_m dx.

The derivative of chi contributes nothing because the gradient of Y_m is tangent to every sphere. Polar integration cancels the common positive radial integral. This proves the angular gradient identity for these functions without presuming a spectral theorem on the sphere. Taking l=0 proves that every Y_m with m>0 has mean zero. Conjugating the identity and interchanging l,m proves orthogonality for distinct degrees. For a finite polynomial restriction, the squared norm and Dirichlet integral consequently split into degree pieces with coefficients m(m+1). Every nonconstant piece has coefficient at least 2, proving (P2) for polynomial restrictions.

Polynomial restrictions are dense in C1 on S^2. For completeness, extend a smoothly to an annulus by radial retraction, multiply by a smooth cutoff supported away from zero, and place the resulting smooth function on a cube. Tensor Bernstein polynomials on the rescaled unit cube approximate both the function and its first derivatives uniformly. The function convergence follows from uniform continuity and the binomial variance estimate. The derivative formula is an average of first grid differences, multiplied by the degree; each such difference is the average of the corresponding first derivative along one grid segment. Uniform continuity of that derivative and the same binomial concentration estimate give uniform derivative convergence. Restricting to the sphere preserves this C1 convergence, since tangential projection has operator norm one. Finite sphere area now passes the polynomial inequality to a. This completes (P2) for precisely the smooth angular slices needed below; no weak slicing theorem is being assumed.

## 3. Unitary polar normalization and radial splitting on the core

For f in the punctured compact smooth core, define

    U(r,omega) = sqrt(4pi) r f(r omega),
    u(r) = integral U(r,omega) dnu(omega),
    W(r,omega) = U(r,omega)-u(r).

All radial functions are smooth and supported in a fixed compact subinterval of (0,infinity). The polar measure identity gives

    ||f||_2^2 = integral integral |U|^2 dr dnu,
    integral W(r,omega) dnu(omega) = 0.

The radial derivative identity

    integral |d(rF)/dr|^2 dr = integral r^2 |F'|^2 dr

holds for every such compactly supported radial slice F. It follows by expanding the left side and integrating r d|F|^2/dr; both endpoint terms vanish. Consequently

    q_Z[f] = integral integral [
       (1/2)|partial_r U|^2 + |grad_S U|^2/(2r^2)
       - (Z/r)|U|^2 ] dr dnu.                                (P5)

There is no hidden r^2 factor remaining in (P5). The factor sqrt(4pi) is required because dnu is probability area measure.

The angular average gives orthogonal decompositions for the norm, radial derivative term and radial potential term; differentiating the zero angular mean is legitimate for these smooth compact functions. The angular derivative of u is zero. Thus (P5) is the sum of the radial energy of u and the corresponding energy of W.

By (P2), the latter satisfies

    q[W] >= integral dnu integral [
       (1/2)|partial_r W|^2 + |W|^2/r^2 - (Z/r)|W|^2 ] dr.

For every radial slice w=W(.,omega), integration by parts gives, with C=d/dr-2/r+Z/2,

    ||Cw||_2^2 = ||w'||_2^2 + 2||w/r||_2^2
                  -2Z integral |w|^2/r + (Z^2/4)||w||_2^2.

Therefore

    q[W] >= -(Z^2/8)||W||_2^2.                               (P6)

This estimate uses only the sharp mean-zero angular inequality; it does not require a complete spherical-harmonic basis, the hydrogen excited spectrum, or an assumed physical complement bound.

## 4. The radial orthogonal branch

The separate half-line lemma uses H1_0(0,infinity), defined by closure of compact smooth functions in the first-derivative graph norm. Put

    A=d/dr-1/r+Z,  B=-d/dr-1/r+Z,  C=d/dr-2/r+Z/2.

Half-line Hardy makes these actual L2 maps on H1_0. For compact smooth functions, then by graph density for all H1_0 inputs, the exact identities are

    ||Av||^2 = ||v'||^2 -2Z integral |v|^2/r + Z^2||v||^2,
    ||Bv||^2 = ||Cv||^2 + (3Z^2/4)||v||^2,
    ||Bv||^2 = ||v'||^2
                + integral [2/r^2-2Z/r+Z^2]|v|^2.             (P7)

The last bracket is 2(1/r-Z/2)^2+Z^2/2, so ||v'||<=||Bv||. Together with the middle inequality this controls the complete H1 norm by ||Bv||. It makes ran B closed: a convergent sequence Bv_n makes v_n Cauchy in H1_0, and Hardy gives convergence of v_n/r to identify the limiting output.

The orthogonal complement of ran B consists exactly of multiples of g(r)=r exp(-Zr). Orthogonality against compact smooth tests is the local distributional ODE

    h' - h/r + Zh = 0.

On any compact interval within (0,infinity), multiplication by the smooth integrating factor exp(Zr)/r makes its weak derivative zero, hence it is constant there; overlapping intervals give one global constant. Conversely, g belongs to H1_0, satisfies Ag=0, and the integration identity <Av,w>=<v,Bw> shows g is orthogonal to ran B. This is a closed-range proof, not a claim that a formal differential adjoint already has a particular maximal domain.

For v orthogonal to g, write v=Bw. The bound in (P7) gives ||w||<=2||v||/(sqrt(3) Z), and integration by parts yields

    ||v||^2 = <Av,w> <= ||Av|| ||w||.

For v=0 the desired bound is immediate; otherwise cancellation gives ||Av||^2 >= (3Z^2/4)||v||^2. The first identity in (P7) then proves

    (1/2)||v'||^2 - Z integral |v|^2/r >= -(Z^2/8)||v||^2.    (P8)

All statements about complex functions use the real part of the relevant sesquilinear identities when expanded into quadratic expressions.

Normalize g to g0=2 Z^(3/2) r exp(-Zr), whose norm is one by the exact elementary radial integral. Since Ag0=0, decompose an arbitrary radial u as <g0,u>g0+u_perp and apply (P8). The A identity supplies zero cross energy and yields

    q[u] >= -(Z^2/8)||u||^2 -(3Z^2/8)|<g0,u>|^2.             (P9)

The actual polar normalization in section 3 gives <g0,u>=<phi_Z,f>. Combining (P6) and (P9) proves (P1) on the punctured core.

## 5. Extension, physical meaning and spin

For an H1-convergent punctured core sequence f_n to f, both the norm and the phi_Z inner product converge. The Coulomb form term also converges: its absolute difference is at most

    Z ||f_n-f||_2 (||f_n/|x|||_2+||f/|x|||_2),

which tends to zero by Hardy and boundedness of the H1 sequence. The kinetic term converges by the first-derivative norm convergence. This proves (P1) on the actual weak H1 domain.

The normalized ground-state transform f=phi_Z a converts the shifted energy into (1/2) integral phi_Z^2 |grad a|^2, whenever the weighted expression is interpreted through the form closure. Accordingly, the ordinary weighted-gradient Poincare constant is 4/(3Z^2). The number 8/(3Z^2) is instead the reciprocal of the energy gap when the gradient form includes its factor one half. Mixing these conventions would cause a factor-two error.

For full one-electron spin, sum (P1) over the two spin components. The exceptional subspace is phi_Z tensor C^2, which has dimension two, and the rank-one scalar term becomes the squared norm of projection onto this full two-dimensional subspace. Orthogonality to one chosen spin ground vector alone is insufficient: the other spin ground vector remains at -Z^2/2.

The proof does not on its own formalize tensor-product two-electron comparisons. Such a comparison must preserve the full simultaneous-permutation fermionic structure; the two-particle product of one-electron ground projections has rank one only after restricting to the two-electron fermionic space.

## 6. Primary comparison and current formal boundary

Teschl's author-hosted text defines the scalar operator -Delta-gamma/r on H2(R^3); Theorem 10.9 gives its discrete levels and scalar ground multiplicity, while Theorem 10.10 gives a radial first-order factorization. Setting gamma=2Z and dividing the operator by two gives the present ground and first-excited energies. These classical results provide a primary-source comparison, not a new mathematical axiom or a Lean proof of the complement. The argument above isolates only the angular inequality and one half-line factorization needed for (P1), avoiding a supplied complete excited spectrum. Source: [Mathematical Methods in Quantum Mechanics, sections 10.2 and 10.4](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf), inspected at the author's site. No novelty claim is made.

Formal components already available: the actual H1/H2 Coulomb domains and forms, Hardy multiplication and H1 form continuity, the explicit hydrogen ground eigenfunction and norm, and spectral/variational identification. Remaining new formal obligations for this route are the punctured H1 core, the angular polynomial/gradient identities and C1 density, actual polar gradient decomposition on that core, and the half-line closed-range/ODE argument. None is silently passed as an assumed final physical complement theorem.

Frozen baseline commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. All changes use new continuation files; frozen and successful prior sources are unchanged.
