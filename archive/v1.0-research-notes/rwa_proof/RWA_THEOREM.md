> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Remainder weighted analyticity for the physical two-electron ground state

**PROVEN — paper proof.** This file proves the exact RWA statement in the
request. It does not claim Lean verification or an approximation theorem.
The new ingredient is a uniform instantiation of a verified
analytic-hypoellipticity estimate on rescaled pair charts.

## 1. Statement

Fix an integer \(Z\ge2\). Let \(\psi_Z\) be the actual normalized positive
spatial ground state, with the spin singlet understood, of
\[
H_Z=-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u,\qquad
D(H_Z)=H^2(\mathbb R^6)\cap L^2_{\rm sym}.
\]
Reuse the established self-adjointness, domain, positivity and rotational
invariance. Put \(S=r+s,\ T=\rho^2=r^2+s^2,\ q=x_1\cdot x_2\),
\(\psi_0=\psi_Z(0)\), and \(f=-ZS+u/2\). The previously established
extraction defines the actual function
\[
\mathcal R_Z=e^{-f}\psi_Z-\kappa_Z\psi_0q\log T,\qquad
\kappa_Z=Z(2-\pi)/(3\pi).
\]
Let \(\widehat{\mathcal R}_Z\) denote its reduction to
\[
r=b+c,\quad s=a+c,\quad u=a+b,\quad S=a+b+2c.
\]

There are \(\delta,A,C>0\), depending on fixed \(Z\) but not on the point
or derivative order, such that
\[
\boxed{
|\partial^\nu(\widehat{\mathcal R}_Z-\psi_0)(a,b,c)|
\le CA^{|\nu|}|\nu|!\,S^{1/2-|\nu|}
}
\tag{RWA}
\]
for every \(\nu\in\mathbb N_0^3\) and every closed-octant point with
\(0<S<\delta\). Derivatives on nonvertex strata are those of the unique
local real analytic extensions.

In fact the proof gives the stronger weight \(S^{1-|\nu|}\).
Choosing \(\delta\le1\) proves the requested strict range with
\(\sigma=1/2\); more generally it implies each fixed \(0<\sigma<1\).
There is no silent replacement by finite-order or Gevrey regularity.

## 2. Source inputs and what is new here

The source audit is completed in
[KS_SOURCE_AUDIT.md](KS_SOURCE_AUDIT.md),
[RESOLVED_SOURCE_AUDIT.md](RESOLVED_SOURCE_AUDIT.md), and
[FOCK_SOURCE_AUDIT.md](FOCK_SOURCE_AUDIT.md). The load-bearing analytic
inputs here are:

1. Fournais et al., [math-ph/0312060](https://arxiv.org/pdf/math-ph/0312060),
   Theorem 1.1, DOI
   [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6):
   the already verified local factorization. Its local Lipschitz
   consequence is used to bound a rescaled amplitude, not to infer higher
   derivatives.
2. Grušin, Theorem 5.1 and Proposition 5.1, equations (5.5),
   (5.14), (5.20)–(5.24), DOI
   [10.1070/SM1971v013n02ABEH001033](https://doi.org/10.1070/SM1971v013n02ABEH001033):
   the all-order factorial induction for the specified Grushin class.
   Its common-input, scale-uniform specialization is proved in
   [UNIFORM_ANALYTIC_AUDIT.md](UNIFORM_ANALYTIC_AUDIT.md).
   The original formulas were checked in the archived primary English PDF.
3. Fournais et al., [0806.1004](https://arxiv.org/html/0806.1004),
   Lemma 4.3 and Proposition 4.4, DOI
   [10.1007/s00220-008-0664-5](https://doi.org/10.1007/s00220-008-0664-5):
   quantitative descent of an analytic KS lift to analytic-plus-distance
   form. Their proof turns bounds \(C_2M_2^{|\beta|+|\gamma|}\) on lifted
   coefficients into physical radii \(1/(4M_2^2)\) and \(1/(2M_2)\).

Neither qualitative analyticity nor a convergence assertion about formal
Fock solutions is an input for uniformity. The new proof supplies the
common analytic coefficient bounds, common maximal estimate, uniform
finite-order initialization, and the distance-coordinate chart cover.

## 3. Fixed normalized geometry and the small-amplitude equation

Consider the compact reduced shell
\[
\mathcal K=\{(a,b,c)\in[0,\infty)^3:1/2\le S\le2\}.
\]
Its Cartesian preimage is compact as well. Distinct pair-collision sets
do not intersect there: \(r=0\) forces \(s=u=S\), \(s=0\) forces
\(r=u=S\), and \(u=0\) forces \(r=s=S/2\). Thus small fixed tubes about
these three sets can be chosen disjoint with the other two distances
bounded below by a fixed \(d>0\). Compactness permits a finite cover by
these pair charts and collision-free Cartesian charts. All these choices
are made at normalized scale, before choosing \(\varepsilon\).

On a slightly larger fixed Cartesian shell define
\[
U_\varepsilon(X)=
\frac{\psi_Z(\varepsilon X)-\psi_0}{\varepsilon},
\qquad 0<\varepsilon\le\varepsilon_0.
\tag{R1}
\]
Choose \(\varepsilon_0\) small enough that its physical arguments lie in
a fixed ball of local Lipschitz regularity. If \(L_Z\) is a Lipschitz
constant there, then \(|U_\varepsilon(X)|\le L_Z|X|\). Thus its \(L^2\)
and \(L^\infty\) norms on every fixed chart are uniformly bounded.
Its exact distributional equation is
\[
[-\tfrac12\Delta+\varepsilon V-\varepsilon^2E_Z]U_\varepsilon
=(-V+\varepsilon E_Z)\psi_0.
\tag{R2}
\]
The full conjugated/reduced equation, including its nonanalytic
directional coefficients and all scaling powers, is derived separately in
[REMAINDER_EQUATION.md](REMAINDER_EQUATION.md).
We estimate (R2) in lifted coordinates to avoid treating those individual
directional coefficients as analytic.

## 4. Uniform analytic pair lifts

On an electron–nucleus chart \(X_1=K(y),\ X_2=t\), the KS transform
satisfies \(|K(y)|=|y|^2\). The lift of (R2) is
\[
Q_\varepsilon(U_\varepsilon\circ K)
=-\psi_0B_\varepsilon/\varepsilon,\qquad
Q_\varepsilon=-\Delta_y-4|y|^2\Delta_t+B_\varepsilon,
\]
\[
B_\varepsilon=-8\varepsilon Z+
8\varepsilon|y|^2\left(-Z/|t|+1/|K(y)-t|\right)
-8\varepsilon^2E_Z|y|^2.
\tag{R3}
\]
The denominator \(|X_1|\) has been cleared exactly; the other two are
bounded away from zero on the fixed chart. A common small complex
neighborhood avoids their quadratic zeros. Consequently
\[
\sup|D^\eta B_\varepsilon|
\le\varepsilon M_B A_B^{|\eta|}|\eta|!,
\tag{R4}
\]
with constants independent of \(\varepsilon,\eta\); the right side in
(R3) has the corresponding uniform bound.

The electron–electron chart \(X=X_1-X_2,\ t=(X_1+X_2)/2\) has the fixed
principal part \(-\Delta_y-|y|^2\Delta_t\), and coefficient
\[
4\varepsilon+
4\varepsilon|y|^2[-Z/|t+K(y)/2|-Z/|t-K(y)/2|]
-4\varepsilon^2E_Z|y|^2.
\tag{R5}
\]
It has the same properties. There is no additional collision in either
normalized chart.

Here is the uniform argument, not an appeal to pointwise analyticity.
For \(P_c=-\Delta_y-c|y|^2\Delta_t\), \(c=4\) or \(1\), Fourier
transformation in \(t\) gives the four-dimensional oscillator
\(-\Delta_y+c|\xi|^2|y|^2\), with lower bound
\(4\sqrt c|\xi|\). Integration by parts gives the common maximal estimates
in (U2)–(U5) of the uniform audit, including unweighted \(D_t\) and \(D_y^2\).
If \(\varepsilon_0 M_B C_P\le1/2\), where \(C_P\) is the fixed
compact-support \(L^2\) bound for \(P_c\), the lower-order perturbation
is absorbed. The result is one constant in Grušin (5.5).

Caccioppoli on fixed nested cylinders controls \(D_yU_\varepsilon\) and
\(|y|D_tU_\varepsilon\). Applying the maximal estimate to a cutoff then
controls \(D_tU_\varepsilon\) and \(D_y^2U_\varepsilon\).
Tangential derivatives commute with \(P_c\), so a finite induction gives
any specified finite number of tangential derivatives. The equation,
viewed as an elliptic equation in \(y\) with \(L^2_t\)-valued unknown,
then gives a uniform \(H^{12}\) bound on a smaller fixed cylinder.
All cutoff gaps and the number of these initialization steps are fixed.
The uniform audit provides their commutators and the inductive equations.

Grušin's factorial induction now has common inputs: its compact-support
estimate, analytic coefficient/source bounds, and the finitely many
starting derivative norms up to its threshold \(r_0=8\).
Equations (5.21)–(5.23) therefore admit one common induction constant.
The fixed Sobolev embedding and Stirling step (5.24) yield
\[
\sup |D^\eta(U_\varepsilon\circ K)|
\le C_K A_K^{|\eta|}|\eta|!,
\tag{R6}
\]
on smaller fixed charts. Neither \(C_K\), \(A_K\), nor the chart radius
depends on \(\varepsilon\).
The direct uniform proof includes distributional solutions: qualitative
hypoellipticity first licenses differentiations, while the energy and
maximal estimates supply all quantitative constants.

On collision-free compact Cartesian patches the same conclusion for
\(U_\varepsilon\) follows by the ordinary elliptic factorial induction:
the principal part is the constant Euclidean Laplacian; all distances
are at least \(d>0\) on a slightly larger patch; and (R2) has uniformly
analytic coefficients and source. For explicit input to that induction,
the compact-support estimate is
\(\|D^2v\|_2=\|\Delta v\|_2\), with Poincaré controlling lower derivatives;
the small potential is absorbed as above. Differentiation has no
principal-coefficient commutators. On nested balls the potential
commutators are
\(\sum_{0<\eta\le\nu}{\nu\choose\eta}
D^\eta(\varepsilon V-\varepsilon^2E_Z)D^{\nu-\eta}v\).
The same shrinking-domain factorial induction, now with ordinary
derivatives, has common coefficients and fixed finite initial norms.
This use of elliptic analyticity is entirely in nonsingular Cartesian
patches; it is not an invocation on the degenerate perimetric operator.

## 5. Quantitative descent to ordinary distances, including all boundary strata

Apply the verified KS descent to (R6). In each nuclear chart,
\[
U_\varepsilon(X,t)
=A_\varepsilon(X,t)+|X|B_\varepsilon^{\,\rm dec}(X,t),
\tag{R7}
\]
where both coefficients have common Cartesian analytic radii and common
holomorphic bounds on slightly smaller polydiscs. The superscript
distinguishes this decomposition coefficient from the operator potential.
The fiber-invariance hypothesis in the KS descent is satisfied because
the lifted function is the actual pullback of \(U_\varepsilon\) by \(K\);
it is constant on every KS fiber.
Indeed divide the factorial bound in (R6) by the multi-index factorial;
\(|\eta|!/\eta!\le7^{|\eta|}\), giving a common geometric coefficient
bound to which Proposition 4.4 applies. Geometric summation on smaller
polydiscs supplies common bounds for both descended coefficients.

The decomposition is unique. If \(A(X)+|X|B(X)=0\) with analytic \(A,B\),
restrict to \(X=tv\). Analytic continuation in \(t\) from \(t>0\) gives
\(A(tv)=-t|v|B(tv)\) also for \(t<0\), while the original identity gives
the opposite sign. Hence \(A=B=0\). This argument allows all spectator
coordinates as parameters. Rotational invariance of \(U_\varepsilon\)
therefore gives invariance of its separate analytic coefficients.

Choose a representative spectator \(t=se_3\), and write
\(X=(x,y,z)\). Each coefficient is invariant under rotations of \((x,y)\).
Its convergent Taylor series consequently has the form
\[
\sum_{m,j,\ell\ge0}
d_{mj\ell}(x^2+y^2)^m z^j(s-s_0)^\ell.
\tag{R8}
\]
This passage is quantitative. If the Cartesian function is bounded by
\(M\) on a polydisc of radius \(h\), restriction to \(y=0\) shows
\[
|d_{mj\ell}|\le M h^{-2m-j-\ell}.
\]
Thus it is holomorphic in the independent variables
\((w,z,s-s_0)\) for \(|w|<h^2,\ |z|<h,\ |s-s_0|<h\), with bound \(8M\)
on the corresponding half-radius polydisc. No derivative-order-dependent
coordinate constant has been introduced.

Now substitute
\[
z=\frac{r^2+s^2-u^2}{2s},\qquad w=r^2-z^2.
\tag{R9}
\]
The spectator satisfies \(s\ge d\). On a fixed sufficiently small complex
distance polydisc about \((0,s_0,s_0)\), denominators stay separated
and (R9) maps into the preceding domain. Its radius depends only on
\(d,h,M\) and the fixed compact spectator range. Multiplication of the
second coefficient in (R7) by \(r\) preserves a common analytic bound.
This proves uniform distance-coordinate analyticity at the \(r=0\)
axis, with all three distance derivatives. Exchange gives the \(s=0\) axis.

For the \(u=0\) axis use \(X=X_1-X_2,\ t=(X_1+X_2)/2\). Now
\[
|t|=\sqrt{(r^2+s^2)/2-u^2/4},\qquad
z=\frac{X\cdot t}{|t|}=\frac{r^2-s^2}{2|t|},
\qquad w=u^2-z^2.
\tag{R10}
\]
The denominator \(|t|\) is bounded below, so its positive square-root
branch extends holomorphically on a uniform complex neighborhood.
The same argument applies to the descended analytic-plus-\(u\) function.

At a noncollision collinear point, use \(X_2=se_3\), \(X_1=(x,y,z)\).
Cartesian analyticity and \(SO(2)\) invariance give (R8) near
\((w,z,s)=(0,z_0,s_0)\). Formula (R9) is analytic there because
\(s_0\ge d\). These charts cover each open face:
\(a=0\) means \(r=s+u\), \(b=0\) means \(s=r+u\), and \(c=0\) means
\(u=r+s\). These faces are not physical collisions.

For an interior noncollinear point \(w>0\), a fixed local square-root
branch for a planar representative gives analytic distance coordinates.
On the compact portion outside the collinear and pair charts its
denominators have a common positive lower bound. This covers the remaining
interior. Thus neither a vanishing Cartesian triangle area nor a pair
axis was hidden in a generic inverse-coordinate constant.

Choose the smaller chart cores so that they cover \(\mathcal K\), while
retaining their larger analytic neighborhoods. Take a finite subcover of
these cores, then take the minimum of their retained distance radii and
the maximum of their analytic bounds. By the Lebesgue-number property
of this finite open cover
of a compact set, every point of \(\mathcal K\) has a complex polydisc
of one fixed radius \(r_*>0\) on which its local extension is bounded
by one \(M_*>0\), for every \(\varepsilon\le\varepsilon_0\).
The linear distance-to-perimetric map changes these by fixed factors
only. Specifically, a perimetric sup-norm perturbation of size \(r_*/2\)
changes each distance by at most \(r_*\).

Extensions from adjacent charts agree wherever required. Their difference
vanishes on the physical open interior approaching the common boundary
point; the real analytic identity theorem makes their germs identical.
This establishes compatibility of all boundary derivatives, without
imposing Dirichlet, Neumann, or arbitrary face data.

We have therefore proved: for some \(r_*,M_*>0\), every normalized
point \(z_0\) with \(S(z_0)=1\) admits a holomorphic extension of
\[
\widehat\psi_Z(\varepsilon z)-\psi_0
\]
to \(|z-z_0|_\infty<r_*\) bounded there by \(M_*\varepsilon\),
uniformly for \(0<\varepsilon\le\varepsilon_0\). Call this assertion (R11).

## 6. Extraction, a common analytic radius, and Cauchy's estimate

Shrink \(r_*\) by a fixed factor if needed. On all the polydiscs in
(R11), \(f(z)\) is bounded, \(q(z)\) is bounded, and the polynomial
\(T(z)=(b+c)^2+(a+c)^2\) stays in a common complex neighborhood
separated from zero. At real centers \(T\ge1/2\). Thus a branch of
\(\log T\) is holomorphic with one common bound.

The scaled actual remainder is exactly
\[
\begin{aligned}
\widehat{\mathcal R}_Z(\varepsilon z)-\psi_0
={}&e^{-\varepsilon f(z)}
[\widehat\psi_Z(\varepsilon z)-\psi_0]
+[e^{-\varepsilon f(z)}-1]\psi_0\\
&-\kappa_Z\psi_0\varepsilon^2q(z)
[2\log\varepsilon+\log T(z)].
\end{aligned}
\tag{R12}
\]
If \(|f|\le F_*,\ |q|\le Q_*,\ |\log T|\le L_*\) on these polydiscs,
and \(0<\varepsilon\le\min(1,\varepsilon_0)\), its holomorphic norm is
at most \(M_R\varepsilon\), where one may take
\[
M_R=e^{F_*}(M_*+F_*|\psi_0|)
+|\kappa_Z\psi_0|Q_*(2/e+L_*).
\tag{R13}
\]
This uses \(\varepsilon|\log\varepsilon|\le1/e\).
The remaining higher logarithms of the actual state, if present, have
already been controlled through the PDE; none is discarded.

Cauchy's estimate on a smaller common radius \(r_*/2\) gives, for all
multi-indices,
\[
|\partial_z^\nu
[\widehat{\mathcal R}_Z(\varepsilon z)-\psi_0]_{z=z_0}|
\le M_R\varepsilon(2/r_*)^{|\nu|}\nu!.
\]
For an arbitrary requested point \(x=(a,b,c)\), set
\(\varepsilon=S(x)\), \(z_0=x/\varepsilon\). The derivatives are taken
with \(\varepsilon\) fixed at this step; the chain rule therefore gives
\[
|\partial_x^\nu(\widehat{\mathcal R}_Z-\psi_0)(x)|
\le M_R(2/r_*)^{|\nu|}\nu!\,S(x)^{1-|\nu|}.
\tag{R14}
\]
Take
\(\delta=\min(1,\varepsilon_0)\), \(A=\max(1,2/r_*)\), \(C=M_R\).
Since \(\nu!\le|\nu|!\) and \(S^1\le S^{1/2}\) on \(0<S\le1\),
(R14) proves exactly (RWA).

## 7. Uniform-constant dependency audit

The constants enter in this order, with none depending on derivative
order or the spatial scale:

1. Fixed normalized shell and a finite collision/collinearity chart cover;
   its spectator separation \(d\), larger chart radii, and cutoff gaps.
2. Fixed \(Z,E_Z,\psi_0\), and a physical Lipschitz bound on a fixed ball.
3. Common complex coefficient radius and bounds \(M_B,A_B\), obtained
   from the explicit separated square roots in (R3) and (R5).
4. The oscillator/Poincaré constants \(C_0,C_P\); choose
   \(\varepsilon_0\le(2M_BC_P)^{-1}\) and small enough for the physical ball.
5. Uniform finite initialization \(C_{12}\), followed by the common
   induction constant in Grušin (5.21)–(5.23) and the fixed
   seven-dimensional Sobolev embedding.
6. Quantitative KS coefficient descent, the elementary invariant-series
   bounds (R8), and fixed rational/square-root chart maps (R9)–(R10).
   Taking a finite minimum/maximum gives \(r_*,M_*\).
7. The explicit extraction bound (R13) and final choices after (R14).

The finite bootstrap is not iterated indefinitely to infer a factorial
bound. The verified all-order induction is the step that supplies that
bound. Uniformity is established on normalized charts before returning
to physical scale.

The proof establishes regularity of the actual physical remainder on the
entire requested closed octant away from its vertex. It leaves open, until
separately proved, realization of its local approximation by the exact
dyadic dictionary, a common global witness with controlled exterior tail,
and the algorithmic composition in Theorem T.
