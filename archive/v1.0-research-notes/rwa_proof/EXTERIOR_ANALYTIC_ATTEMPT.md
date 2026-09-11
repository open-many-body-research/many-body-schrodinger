> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Exterior distance analyticity with polynomial radius loss

**PROVEN (paper proof).** This supplies an exterior analytic input for the actual two-electron atomic ground state. It proves no global dictionary approximation or graph residual by itself.

## Statement

Fix \(Z\ge2\) and \(D>0\). Let \(\widehat\psi_Z(a,b,c)\) be the rotationally reduced normalized positive ground state, with \(S=a+b+2c\). There are \(c_{Z,D},M_{Z,D}>0\), independent of the point and of derivative order, such that every \(x=(a,b,c)\in[0,\infty)^3\) with \(S(x)\ge D\) has a compatible holomorphic extension to the complex polydisc
\[
\mathbb D_x=\{z\in\mathbb C^3:|z-x|_\infty<c_{Z,D}/(1+S(x))\},
\]
bounded there by \(M_{Z,D}\). Consequently
\[
|\partial^\nu\widehat\psi_Z(x)|
\le M_{Z,D}\left[\frac{2(1+S(x))}{c_{Z,D}}\right]^{|\nu|}\nu!.
\tag{E1}
\]
The radius loss has polynomial degree one, and the amplitude has degree zero. The constants need not be numerically optimal or computable for this regularity assertion.

Equivalently, on the fixed normalized shell
\[
K=\{y\in[0,\infty)^3:1/4\le S(y)\le2\},
\]
the functions \(F_\tau(y)=\widehat\psi_Z(\tau y)\), for \(\tau\ge4D\), have compatible holomorphic neighborhoods of radius at least
\[
r_\tau=c'_{Z,D}(1+\tau)^{-2},
\qquad \|F_\tau\|_{\mathrm{hol}}\le M_{Z,D}.
\tag{E2}
\]
Thus no exponential-in-outer-radius analytic constant is required. Constants for the finitely bounded interval of positive scales can be incorporated by decreasing \(c'\).

## 1. A global real amplitude bound

This step ensures that passing to a KS lift does not introduce an uncontrolled norm at distant pair collisions.

Set \(F=-ZS+u/2\) and \(L=\sqrt2(Z+1/2)\), so that \(|\nabla F|\le L\) and distributionally \(\Delta F=2V\). On a ball \(B_2(x_0)\), put
\[
\phi_{x_0}(x)=e^{-F(x)+F(x_0)}\psi_Z(x).
\]
The multiplier and its first derivatives are bounded uniformly in \(x_0\), because \(|F(x)-F(x_0)|\le2L\). The exact equation is
\[
\Delta\phi_{x_0}
=-2\nabla F\cdot\nabla\phi_{x_0}
-\bigl(|\nabla F|^2+2E_Z\bigr)\phi_{x_0}.
\tag{E3}
\]
Its first-order and zero-order coefficients are uniformly bounded; their derivatives are not used.

The real function \(\phi_{x_0}\) is positive and belongs locally to \(H^1\). Its \(L^2(B_2(x_0))\) norm is at most \(e^{2L}\), since the ground state is normalized. The previously proved bound \(|E_Z|\le Z^2\) gives uniform coefficient bounds
\[
|b|=|2\nabla F|\le B:=2L,\qquad
|c|=||\nabla F|^2+2E_Z|\le C_0:=L^2+2Z^2.
\]

Here is a direct Moser argument, avoiding any assumption that \(H^2(\mathbb R^6)\) embeds in \(L^\infty\), and avoiding a new regularity theorem for the nonsmooth drift. For \(v=\phi_{x_0}\), test (E3) against \(\eta^2v^{p-1}\), \(p\ge2\), and write \(w=v^{p/2}\). The test is licensed initially by truncating the powers at a finite level and then using monotone convergence. Integration by parts and Young's inequality give
\[
\|\eta\nabla w\|_2^2
\le8\|w\nabla\eta\|_2^2+(2B^2+pC_0)\|\eta w\|_2^2,
\]
\[
\|\nabla(\eta w)\|_2^2
\le18\|w\nabla\eta\|_2^2+(4B^2+2pC_0)\|\eta w\|_2^2.
\tag{E4}
\]
For clarity, the unabsorbed left coefficient is \(4(p-1)/p^2\); the cross terms are bounded by \((4/p)XY+(2B/p)XT+C_0T^2\), where \(X=\|\eta\nabla w\|_2\), \(Y=\|w\nabla\eta\|_2\), \(T=\|\eta w\|_2\). Absorbing one quarter of the left coefficient in each cross term proves (E4).

The Euclidean Sobolev inequality in dimension six holds with the sufficient constant three:
\[
\|g\|_3\le3\|\nabla g\|_2\qquad(g\in C_c^\infty(\mathbb R^6)).
\]
One elementary derivation starts from the fundamental theorem of calculus in each coordinate and iterated Hölder, which give
\(\|f\|_{6/5}\le\prod_{i=1}^6\|\partial_i f\|_1^{1/6}\le\|\nabla f\|_1\).
Apply this to \(f=|g|^{5/2}\), then use Cauchy–Schwarz; the resulting constant is \(5/2<3\). Density extends it to the compactly supported \(H^1\) functions in (E4).

For concentric radii \(1\le r<R\le2\), take \(|\nabla\eta|\le2/(R-r)\). Put
\[
K_Z=72+4B^2+2C_0=72+18L^2+4Z^2.
\]
Equations (E4) and Sobolev yield
\[
\|v\|_{L^{3p/2}(B_r)}
\le[9K_Zp(R-r)^{-2}]^{1/p}\|v\|_{L^p(B_R)}.
\]
Iterate with \(p_j=2(3/2)^j\) and \(R_j=1+2^{-j}\). The convergent product is bounded by \(2^{18}K_Z^{3/2}\), since
\(\sum 1/p_j=3/2\) and \(\sum j/p_j=3\).
Returning to \(\psi_Z=e^{F-F(x_0)}v\) gives the explicit sufficient bound
\[
\boxed{\ \|\psi_Z\|_\infty
\le2^{18}K_Z^{3/2}e^{3L}=:M_\infty(Z).\ }
\tag{E5}
\]
Only bounded real coefficients were used for this amplitude estimate. Analyticity below is obtained from the original Coulomb equation in Cartesian or KS charts, not by treating the nonsmooth drift in (E3) as analytic.

## 2. Fixed physical analytic charts, uniformly over the exterior

Take \(\eta=\min(D/100,1/100)\). If \(r<4\eta\) and \(S\ge D\), then \(s\ge D-4\eta\) and \(u\ge D-8\eta\). If \(u<4\eta\), then \(r,s\ge(D-4\eta)/2\). Thus distinct pair strata have disjoint sufficiently small tubes throughout this exterior, with all spectator denominators separated by a positive fixed number.

On an electron–nucleus pair chart, centered at \((0,t_0)\), \(|t_0|\ge D/2\), choose one fixed sufficiently small physical scale \(h>0\). Write
\[
x_1=hX,\qquad x_2=t_0+ht,\qquad X=K(y).
\]
The lifted operator is
\[
-\Delta_y-4|y|^2\Delta_t
-8hZ+
8h^2|y|^2\left(-\frac Z{|t_0+ht|}
+\frac1{|hK(y)-t_0-ht|}\right)
-8h^2E_Z|y|^2.
\tag{E6}
\]
On fixed normalized cylinders, the coefficient bounds and complex radii are uniform in \(t_0\), even when \(|t_0|\to\infty\). Indeed the two spectator distances are bounded below, and reciprocal Euclidean norms have common analytic bounds under complex perturbations smaller than a fixed fraction of that distance. The coefficients in (E6) are \(O(h)\) in that common analytic norm.

Choose \(h\) smaller if necessary to meet the absorption threshold in [UNIFORM_ANALYTIC_AUDIT.md](UNIFORM_ANALYTIC_AUDIT.md), equations (U5)–(U6). This is a single fixed choice depending on \(Z,D\). The lifted unknown has uniform \(L^2\) norm by (E5) and the finite normalized cylinder volume. The verified uniform factorial induction, followed by quantitative KS descent, therefore gives
\[
\psi_Z(x_1,x_2)=A_{t_0}(x_1,x_2)+rB_{t_0}(x_1,x_2),
\tag{E7}
\]
where both analytic coefficients have common physical radii and common holomorphic bounds. The rescaling of the second coefficient introduces only the fixed factor \(h^{-1}\).

The electron–electron chart \(X=x_1-x_2,\ t=(x_1+x_2)/2\) has the same argument, with the fixed principal operator \(-\Delta_y-|y|^2\Delta_t\), and gives analytic-plus-\(u\) form. Use the conservative lower bound \(|t_{\rm center}|\ge D/4\) for projected centers of its tubes: when \(u<4\eta\le D/25\), one has \(r,s>12D/25\) and \(|t|\ge r-u/2>11D/25>D/4\). A projected center need not itself have \(S\ge D\), so using \(D/2\) for every such center would be incorrect. This is only a fixed chart-radius adjustment.

After these pair radii have been chosen, retain smaller fixed pair tubes. The complement has \(r,s,u\ge d_*>0\), with \(d_*\) depending only on \(Z,D\). On it the Cartesian Coulomb equation has common analytic coefficient bounds on fixed-radius balls. The constant-principal-part factorial induction used in [RWA_THEOREM.md](RWA_THEOREM.md), section 4, applies uniformly after choosing the ball radius small enough to absorb the bounded potential. The \(L^2\) input is at most the global norm one. Hence the Cartesian wavefunction has fixed analytic radii and holomorphic bounds on this complement, independently of the center's distance from the nucleus.

There is no compactness assertion about an unbounded set here. Uniformity follows from the explicit lower bounds on the spectator distances, the common amplitude estimate, fixed chart sizes, and fixed operator estimates.

## 3. Pair-axis descent has no exterior radius loss

For the nuclear pair, choose a rotational representative \(x_2=se_3,\ x_1=(x,y,z)\). Uniqueness of the analytic-plus-\(r\) decomposition makes each coefficient in (E7) invariant under rotations in \((x,y)\). The elementary invariant-series argument in [RWA_THEOREM.md](RWA_THEOREM.md), section 5, converts its fixed Cartesian analytic radius into a fixed radius in
\[
w=x^2+y^2,\quad z,\quad s-s_0.
\]
The coefficient bounds remain uniform.

At the axis \((r,s,u)=(0,s_0,s_0)\), use
\[
z=\frac{r^2+(s-u)(s+u)}{2s},\qquad w=r^2-z^2.
\tag{E8}
\]
For a sufficiently small fixed distance polydisc, \(s_0\ge D/2\) ensures \(|z|\le C\delta\), \(|w|\le C\delta^2\), and \(|s-s_0|\le\delta\), with constants independent of large \(s_0\). The potentially large factors in \(s+u\) divide by \(s\). Thus one fixed distance radius works near every nuclear pair axis.

For the electron–electron pair, the analogous quantities are
\[
t_*=\sqrt{(r^2+s^2)/2-u^2/4},\quad
z=\frac{(r-s)(r+s)}{2t_*},\quad w=u^2-z^2.
\tag{E9}
\]
Near \((r,s,u)=(t_0,t_0,0)\), use \(t_0\ge D/4\) so projected tube centers are included. Their variations satisfy
\(|t_*-t_0|\le C\delta,\ |z|\le C\delta,\ |w|\le C\delta^2\)
on a fixed small distance polydisc. The positive square-root branch is uniform. This gives a fixed radius there as well. Shrinking once extends these bounds to the smaller retained pair tubes.

## 4. Collinear and noncollinear conversion: explicit polynomial loss

Outside the pair tubes, choose the electron with the larger nuclear distance as spectator. Thus, after a possible exchange,
\[
s\ge S/2,\qquad r\le s,\qquad u\le S.
\]
This selects a chart at a point; it does not introduce the nonanalytic function \(\max(r,s)\) into any coordinate formula.

Let \(h_*>0\), \(h_*\le1\), be a common small Cartesian radius from section 2, further decreased so that projecting a point within transverse distance \(h_*/16\) to a collinear configuration still keeps it outside all pair collisions. On the reduced representative define
\[
z=\frac{r^2+s^2-u^2}{2s},\quad
w=r^2-z^2.
\]
For complex changes \(|\Delta r|,|\Delta s|,|\Delta u|\le\delta\), with \(\delta\le\min(S/8,1)\), direct algebra gives
\[
|\Delta z|\le9\delta,\qquad
|\Delta w|\le102(1+S)\delta.
\tag{E10}
\]
Indeed \(|s+\Delta s|\ge3S/8\), and
\(|\Delta(r^2+s^2-u^2)|\le(35/8)S\delta\).
Subtract the formula for \(z\), using \(|z|\le r\le S\), to obtain the first bound. Expanding \(w\) then gives
\(20S\delta+82\delta^2\), proving the second.

If \(w<h_*^2/256\), use the fixed Cartesian analytic chart at the collinear projection. Its \(SO(2)\)-invariant series is holomorphic in \(w\) on a fixed radius proportional to \(h_*^2\), and in \(z,s\) on radii proportional to \(h_*\). By (E10), a distance polydisc of radius
\[
\delta=\frac{c_0}{1+S},\qquad
c_0\le\min(D/16,1,h_*^2/2^{20}),
\tag{E11}
\]
maps inside a fixed smaller invariant-series domain.

If \(w\ge h_*^2/256\), use the planar representative
\[
x_1=(\sqrt w,0,z),\qquad x_2=(0,0,s).
\]
The same choice ensures \(|\Delta w|<w/4\), so the positive square-root branch persists, and
\[
|\Delta\sqrt w|
\le 2|\Delta w|/\sqrt w
\le32|\Delta w|/h_*<h_*/16
\]
after decreasing the absolute constant in (E11) if needed. The changes in \(z,s\) are also smaller than the common Cartesian radius. Thus this distance polydisc maps into the original analytic chart. The amplitude bound is the same common Cartesian bound.

If electron labels were exchanged, undo that fixed permutation. The physical function is exchange-symmetric. The conversion from distances to half-perimetric variables is linear: a perimetric perturbation of sup-norm at most \(\delta/2\) changes every distance by at most \(\delta\).

Take \(c_{Z,D}\) to be half the minimum of \(c_0\) and the fixed radii already obtained for the pair tubes, decreasing it once for margins. Take \(M_{Z,D}\) to be the maximum of the common pair and collision-free analytic bounds. These choices prove the holomorphic statement and (E1). At all open faces, edges and their overlaps, germs agree by their common values on the physical real interior. No boundary conditions or arbitrary continuation data are imposed.

## 5. Normalized shells and the scope for dictionary approximation

Under \(x=\tau y\), a physical polydisc radius \(c/(1+S(x))\) becomes at least
\[
\frac{c}{\tau(1+2\tau)}
\ge\frac{c/2}{(1+\tau)^2},
\]
proving (E2). This is an explicit polynomial dependence in the outer scale.

For quantitative use in the Gevrey-cutoff/Chebyshev construction, cover the fixed normalized shell by a cubical grid of mesh proportional to \(r_\tau\). The number of boxes is \(O(r_\tau^{-3})=O((1+\tau)^6)\). Choose cutoffs with supports in enlarged grid boxes. Their overlap multiplicity is an absolute constant, independent of \(\tau\); this is essential when tracking products and sums of cutoffs. Their derivatives have Gevrey-2 bounds
\[
C^k r_\tau^{-k}(k!)^2.
\]
The telescoping weights used in the local proof have the same type of bound, with a fixed larger \(C\), because at any point only the fixed number of overlapping supports can contribute nonzero derivatives. The analytic factors have bounds \(M\,C^k r_\tau^{-k}k!\). Hence one may form the compactly supported Gevrey-2 extension with amplitude and derivative constants polynomial in \(1+\tau\), rather than exponential in the number of boxes.

The Fourier-to-Chebyshev argument in the local dictionary proof can therefore be tracked explicitly. After composition with cosines on a fixed containing cube, one-coordinate derivatives satisfy \(M(C/r_\tau)^k(k!)^2\). Integration by parts, followed by \(k=\lfloor\sqrt{Nr_\tau/(4C)}\rfloor\), bounds a Fourier coefficient by
\[
C M e^{-b_\tau\sqrt N},\qquad b_\tau=c\sqrt{r_\tau}\ge c'/(1+\tau).
\]
Here \(N\) is the largest frequency. There are \(O((N+1)^2)\) frequency triples at that maximum, and a total of two distance derivatives of tensor Chebyshev factors costs at most \(C(N+1)^4\). Hence the coefficient tail is bounded using
\[
\sum_{N>d}(N+1)^6e^{-b\sqrt N}
\le C b^{-14}e^{-b\sqrt d/2}\qquad(0<b\le1).
\]
To check the power fourteen, reserve half the exponential for the tail factor, compare the remaining sum to an integral, and substitute \(t=\sqrt N\); the resulting integral is a constant times \(13!b^{-14}\). Thus symmetric ordinary polynomials of degree at most \(q\) can be selected with
\[
\max_{|\nu|\le2}\sup_K|\partial^\nu(F_\tau-Q_{\tau,q})|
\le C(1+\tau)^{14}
\exp[-c\sqrt q/(1+\tau)].
\tag{E12}
\]
The same coefficient bound gives a polynomial \((1+\tau)^{14}\) prefactor in the bounded-cube norm and in the exterior polynomial-growth estimate used for Poisson weights. Constants in (E12) depend only on the fixed shell, fixed \(Z,D\), and the established common analytic bounds. No exponent depends on the shell number or the outer radius.

This supplies the constant accounting for ordinary polynomial approximation on a growing outer shell. It does not by itself show that the same dictionary element realizes all shells or has a small exterior tail. Those are the separate admissible-witness estimates required in Phase 7. No empirical convergence or physical-tail estimate was used to infer the analytic statement.
