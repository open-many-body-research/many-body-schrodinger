> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Independent adversarial audit of the conditional local dyadic remainder theorem

Audited file: `DYADIC_REMAINDER_ATTEMPT.md`, equations (D1)–(D21), 2026-09-09. This audit is independent of the construction's author. No numerical RATE experiment, certificate computation, or Lean build was performed.

**Verdict:** the conditional implication RWA-type derivative bounds => local physical H² approximation in the exact prescribed dictionary is supported by the argument. I found no substantive mathematical gap or counterexample in the construction. The two clarifications identified below concern details that can be proved directly, not new open hypotheses. This verdict does not prove the physical premise RWA and does not establish global graph RATE.

## 1. The analytic extension and Gevrey step

The rescaled shell stays a fixed positive distance from S=0. The multi-index sum in its Taylor expansion is controlled by

\[
\sum_{|\nu|=k}\frac{k!}{\nu!}
(A_*|h_1|/S)^{\nu_1}(A_*|h_2|/S)^{\nu_2}
(A_*|h_3|/S)^{\nu_3}
=\bigl(A_*|h|_1/S\bigr)^k.
\]

A radius chosen below both a fixed shell-geometric radius and 1/(32A_*) therefore suffices uniformly in tau. The assumed nonvertex boundary analyticity identifies the resulting Taylor extensions with the physical reduced function. Thus no unknown qualitative analytic radius is being used as a uniform radius.

For h(t)=exp(-1/t), the Cauchy-circle estimate in the proof gives

\[
|h^{(k)}(t)|\le k!(2/t)^k e^{-2/(9t)}
\le9^k(k!)^2.
\]

The proposed normalization is valid: on [1/4,3/4], 1/t+1/(1-t)<=16/3<6, so the integral of h(t)h(1-t) is at least exp(-6)/2. Fixed products, integration and affine rescaling preserve a uniform Gevrey-2 estimate. The finite box cover depends on the fixed RWA constants, not on q or tau. Ordered weights chi_i product_(h<i)(1-chi_h) really sum to one wherever some chi_i equals one; no division by a possibly small partition sum occurs.

The composition with cosine is also sound. Grouping the Faà di Bruno terms by l gives the displayed bound with (k!)², not an extra factorial. Repeated integration by parts with k=floor(sqrt(N/(4B_1))) yields at least a factor 4^(-k). The number of three-dimensional Fourier modes at largest frequency N is O(N²), and two polynomial derivatives add only polynomial factors. These factors can be absorbed by reducing the positive constant in exp(-b sqrt(q)). This validates (D3).

## 2. Polynomial growth outside the fitted shell

This was the most important possible instability. It does not produce an uncontrolled q^q factor here. The Fourier/Chebyshev coefficient series is absolutely summable uniformly in tau, including its derivative-weighted versions. For B>=4 and a nonnegative half-perimetric point of S=t>=2, each coordinate has magnitude <=t, and elementary Chebyshev bounds give, for i=0,1,2,

\[
|D_y^iT_k(y/B)|
\le C_B(k+1)^{2i}(1+2|y|/B)^k
\le C_B(k+1)^{2i}t^k.
\]

For |y/B|<=1 use the usual bounded-interval estimates instead. Tensor products have total degree <=q, so the outside bound M(q+1)^4(6t)^q in (D4) is conservative. On the whole fitting cube the derivative series gives a q-independent bound. Thus both parts of (D4) can hold simultaneously. Auxiliary cutoffs affect polynomial coefficients only; no cutoff multiplies the final trial function.

## 3. Poisson shell localization and upper/lower tails

Equation (D7) follows exactly by differentiating the finite Poisson sum. On z<=p the gamma density increases, and on z>=p it decreases. Combining this with p!>=(p/e)^p gives (D9); two derivatives introduce at most the stated polynomial factors after multiplication by t^i. On the compact middle interval the same formulas give the uniform polynomial bound.

The constants in (D10) are valid without numerical estimates. Convexity gives 2/3<log(2)<3/4, so log(2)-1/2>1/8 and 1-log(2)>1/4. The derivatives of the differences in (D10), with respect to log(t), have the needed signs.

For the upper tail the audit gives the explicit integral

\[
\int_2^\infty t^{13}(t/2)^{2q-2p}\,dt
=\frac{2^{14}}{2p-2q-14},\qquad p>q+7.
\]

After taking its square root the exponential factor is 12^q exp(-p/4). Since log(12)<3 and p=256(q+1), this is bounded by exp(-p/8), with ample margin. There is no factor exponential in q log(q) left to defeat the chosen schedule.

On the lower tail, the factors 4^p arising from (4t)^p are cancelled by integrating only over t<=1/4. The potentially singular second-derivative factors are integrable for the actual p>=256. The fitted shell has bounded t and introduces no further scale dependence. The inner Poisson omission is handled by t^i |D_t^i E_p(pt)|<=C(p+1)^3 on t<=2 and the same upper-tail bound on t>=2. The outer and constant omissions have even smaller gamma arguments.

## 4. Physical six-dimensional H² and collision strata

All three identities (D12) check. In particular,

\[
\int_0^1v(1-v)\log(1/|2v-1|)\,dv=2/9
\]

gives the factor 16pi²/9 in the u^(-2) identity. The r^(-2) and s^(-2) factors are 16pi²/3, and the unweighted factor is 8pi²/15.

The generous constant 10^6 in (D11) can be checked directly. Each of the gradients of a,b,c has norm <=2. Thus the physical gradient is bounded by 6F_1, and its Hessian by

\[
36F_2+3F_1(1/r+1/s+2/u).
\]

Squaring with Cauchy–Schwarz and using pi²<10 yields coefficients at most 15552 for the S^5 F_2² term and 13608 for the S^3 F_1² term; the other coefficients are smaller. Hence 10^6 safely dominates every contribution.

**Clarification recommended to the author:** square integrability of the classical derivatives should explicitly be accompanied by weak-derivative removability. Here that argument is immediate. Away from the vertex, gradients remain bounded at each pair collision; boundary fluxes across a radius-epsilon collision cylinder are O(epsilon²). At the triple point, the RWA lift has gradient O(rho^(sigma-1)), so the corresponding spherical flux is O(epsilon^(sigma+4)). Both vanish. The first-derivative argument is easier. Collinear configurations with r,s,u positive are ordinary smooth Cartesian points of the distance map. Thus the computed Hessian is the weak Hessian, with no distributional collision defect.

On a shell of radius tau, volume contributes tau³ to an L² norm while second derivatives cost tau^(-2). This confirms tau^(sigma+1) in (D16)–(D18). Lower derivative terms are absorbed because tau<=delta/4<=1/4. The physical weight at pair axes causes no extra loss. The geometric sum in (D19) is finite with the displayed denominator.

## 5. Index, constants, and scope

The selected first shell satisfies delta/8<tau_(j0)<=delta/4 by minimality of j0. The stated two lower bounds on q ensure j0<=J. Both exponentials in W_j P_j have polynomial degree <=p+q, and the largest node index is J+1. Therefore the exact index is

\[
p+q+2(J+1)=769q+770.
\]

There is no alteration of the exponent set, no reciprocal monomial in the final witness, and no cutoff in the final witness. Electron-exchange symmetrization preserves the estimates. The conjugated physical remainder minus its constant value satisfies the same kind of RWA bound by the product rule; sigma<1 makes the analytic linear-order correction admissible.

Fixed constants in the analytic cover, Gevrey normalization, Fourier decay, and polynomial estimates depend only on the stipulated RWA constants, sigma, delta, Z and the constant amplitude. They need not depend on shell scale or polynomial degree. The argument is existential and does not compute physical RWA constants or prove a bit-complexity bound; it makes no such claim.

The global H² membership claim also passes: distance-polynomial exponentials have integrable collision derivatives and exponentially decaying exterior tails. The proof's polynomial global norm bound is compatible with its tail estimates. However, the constant Poisson approximant has appreciable mass out to radius of order p/Z. Bounded or polynomially growing exterior norm is not small exterior error. Hence the local theorem cannot be normalized and promoted to a global ground-state residual certificate without a separate global construction.

**Audit status:** conditional local approximation theorem PROVEN (paper proof, assuming (D1)); physical RWA and global graph RATE retain their independently established statuses. No new OPEN lemma was found inside this conditional approximation argument.
