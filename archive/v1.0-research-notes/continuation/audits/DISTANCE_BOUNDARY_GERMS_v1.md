> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Quantitative invariant-distance charts and compatible boundary germs

Evidence category: **paper proof**. This document isolates the exact coordinate
and gluing implications after Cartesian analytic bounds have been supplied.
It does not assume an analytic inverse of the distance map at a collinear
configuration. Nor does it assume that agreement on a normalized surface
determines a three-variable holomorphic function.

## 1. The ambient physical variables

For two spatial electron positions let
\[
 r=|x_1|,\qquad s=|x_2|,\qquad u=|x_1-x_2|.
\]
Use the exact perimetric coordinates
\[
 a=(s+u-r)/2,\quad b=(r+u-s)/2,\quad c=(r+s-u)/2.
\]
Their inverse is
\[
 r=b+c,\qquad s=a+c,\qquad u=a+b.                               \tag{B1}
\]
The open set of noncollinear physical distance triples is represented by
\[
 O=(0,\infty)^3\subset\mathbb R^3_{a,b,c}.
\]
The closed physical region is the nonnegative octant. A normalized set of
centers can be the compact convex simplex
\[
 K=\{a,b,c\ge0:a+b+c=1\},
\]
or a compact truncated simplex with a strictly positive lower and finite
upper bound on \(a+b+c\).

In the gluing theorem below all germs have **three complex ambient
variables** \((a,b,c)\), and all local equality statements hold on full
real open subsets of \(O\), including radial neighborhoods of the centers.
The simplex \(K\) is only a set of centers. Equality just on its
two-dimensional surface is insufficient.

The physical scalar function of distances is an explicit hypothesis: the
underlying Cartesian function is invariant under simultaneous rotations
of both spatial vectors, so its value is determined by the distances.
No ground-state uniqueness or rotational invariance is proved in this
coordinate lemma.

## 2. A quantitative SO(2) invariant-series lemma

Fix real centers \(z_0,\sigma_0\in\mathbb R\).
Suppose \(F(x,y,z,\sigma)\) is holomorphic and bounded by \(M\) on
\[
 |x|,|y|,|z-z_0|,|\sigma-\sigma_0|<h,\qquad h>0,
\]
and is invariant under real rotations of \((x,y)\) on its real domain
whenever both arguments are in the domain. Then
\[
 F(x,y,z,\sigma)=G(x^2+y^2,z,\sigma)                              \tag{B2}
\]
where the right side is defined, with \(G\) holomorphic on
\[
 |w|<h^2,\qquad |z-z_0|,|\sigma-\sigma_0|<h.
\]
It has the power series
\[
 G(w,z,\sigma)=\sum_{m,j,\ell\ge0}
 d_{mj\ell}w^m(z-z_0)^j(\sigma-\sigma_0)^\ell,\qquad
 |d_{mj\ell}|\le M h^{-2m-j-\ell}.                               \tag{B3}
\]
In fact \(|G|\le M\) throughout this domain. The weaker bound \(8M\) on
the half polyradii also follows by direct geometric summation.

To prove the algebraic assertion, compare homogeneous Taylor terms in
\((x,y)\) under the rotation, or differentiate the real identity to obtain
\((-y\partial_x+x\partial_y)F=0\). In variables \(v=x+iy,\bar v=x-iy\),
regarded as independent complex polynomial variables, invariance retains
only equal powers. Thus each invariant polynomial is a polynomial in
\(v\bar v=x^2+y^2\). The coefficient of \(w^m(z-z_0)^j
(\sigma-\sigma_0)^\ell\) is exactly the coefficient of
\(x^{2m}y^0(z-z_0)^j(\sigma-\sigma_0)^\ell\) in \(F\); Cauchy's
estimate proves (B3), with no extra exponential conversion factor.

The series (B3) converges normally on the stated domain. For every complex
\(w\) there, choose either square root \(x\) and set \(y=0\).
Then \(|x|<h\), and the series gives
\[
 G(w,z,\sigma)=F(\sqrt w,0,z,\sigma).
\]
This equality is independent of the root and proves the bound \(M\).
It is a bound for a function already proved holomorphic by its series,
not a differentiation rule through the singular square root at zero.

The identity (B2) is asserted only where \(|x^2+y^2|<h^2\), as well as
the original Cartesian restrictions. That intersection is star-shaped
in \((x,y)\); the local series identity extends throughout it. In
particular, the guaranteed \(w\)-domain is not all of the image of the
original Cartesian polydisc, where \(|w|\) could approach \(2h^2\).

## 3. Nuclear collision axis with an explicit radius

Let the center be \((r,s,u)=(0,\sigma_0,\sigma_0)\), \(\sigma_0>0\).
Suppose the actual Cartesian function near \(X=0,t=\sigma_0e_3\) has
\[
 U(X,t)=A(X,t)+|X|B(X,t),
\]
where the separate coefficients are analytic, and their restrictions
\(A(x,y,z,\sigma e_3)\), \(B(x,y,z,\sigma e_3)\) obey Section 2 with
radius \(h\), center \(z_0=0\), and respective bounds \(M_A,M_B\).
Their SO(2) invariance follows if the physical function is rotationally
invariant: uniqueness of analytic-plus-distance decomposition forces
invariance of the separate coefficients under the rotations fixing \(e_3\).
That uniqueness is proved in the sealed quantitative KS descent.

Define
\[
 z={r^2+s^2-u^2\over2s},\qquad w=r^2-z^2.                       \tag{B4}
\]
For
\[
 |r|,|s-\sigma_0|,|u-\sigma_0|<\delta,\qquad
 0<\delta\le\min(1,\sigma_0/4,h/16),
\]
the denominator satisfies \(|s|\ge3\sigma_0/4\), and
\[
 |z|\le4\delta,\qquad |w|\le17\delta^2,\qquad |s-\sigma_0|<\delta.
                                                                  \tag{B5}
\]
Indeed the numerator of \(z\) is \(r^2+(s-u)(s+u)\); its norm is at
most \(\delta^2+5\sigma_0\delta\), yielding even the bound
\((7/2)\delta\). The stated bound is a convenient enlargement.
Equations (B5) map strictly inside the half polyradii of Section 2.
Consequently
\[
 \mathcal U(r,s,u)=G_A(w,z,s)+rG_B(w,z,s)                          \tag{B6}
\]
is holomorphic on this distance polydisc, bounded by
\(M_A+\delta M_B\). It agrees with the actual physical value on its
intersection with the physical open distance region. The equality uses a
real planar representative of the distances and rotational invariance;
it does not prescribe arbitrary values on the collision boundary.
Exchange of the two electrons gives the \(s=0\) axis.

## 4. Electron-pair collision axis

Let the center be \((r,s,u)=(\sigma_0,\sigma_0,0)\), \(\sigma_0>0\).
Use relative and center coordinates \(X=x_1-x_2\),
\(t=(x_1+x_2)/2\). Suppose the analytic-plus-\(|X|\) coefficients restricted
to \(t=\sigma e_3\) have the same kind of SO(2) analytic bounds as in
Section 3, around \(X=0,\sigma=\sigma_0\).

Set
\[
 q=(r^2+s^2)/2-u^2/4,\qquad
 \tau=\sqrt q,\qquad
 z={r^2-s^2\over2\tau},\qquad w=u^2-z^2.                         \tag{B7}
\]
The square root is the branch taking the positive value \(\sigma_0\)
at the center. If
\[
 |r-\sigma_0|,|s-\sigma_0|,|u|<\delta,\qquad
 0<\delta\le\min(1,\sigma_0/16,h/24),
\]
then
\[
 |q-\sigma_0^2|\le3\sigma_0\delta<\sigma_0^2/4,
\quad |\tau|\ge\sigma_0/2,\quad
 |\tau-\sigma_0|\le3\delta,\quad
 |z|\le5\delta,\quad |w|\le26\delta^2.                            \tag{B8}
\]
For the root estimate, its branch has positive real part, so
\(|\tau+\sigma_0|\ge\sigma_0\); use
\(\tau-\sigma_0=(q-\sigma_0^2)/(\tau+\sigma_0)\).
The bound for \(z\) follows by writing its numerator as
\((r-s)(r+s)\). These estimates map into the retained half polyradii.
The holomorphic distance extension is
\[
 \mathcal U(r,s,u)=G_A(w,z,\tau)+uG_B(w,z,\tau),                    \tag{B9}
\]
bounded by \(M_A+\delta M_B\), and agreeing with the actual physical
function on a full real open physical neighborhood.

## 5. Noncollision collinear points and the interior

At a noncollision collinear center choose
\[
 x_2=\sigma_0e_3,\quad x_1=z_0e_3,\quad
 r_0=|z_0|>0,\quad u_0=|z_0-\sigma_0|>0,\quad s_0=\sigma_0>0.
\]
Suppose the Cartesian function, with this representative, satisfies the
analytic SO(2) hypothesis of Section 2 centered at \(z_0,\sigma_0\).
No cusp decomposition is needed at this point. Define
\[
 L_0=r_0+\sigma_0+u_0,\quad C_z=4L_0/\sigma_0,\quad
 C_w=2r_0(1+C_z)+1+C_z^2.
\]
For distance perturbations of sup size \(\delta\le\min(1,\sigma_0/4)\),
(B4) satisfies
\[
 |z-z_0|\le C_z\delta,\qquad |w|\le C_w\delta.                    \tag{B10}
\]
For the first estimate, multiply \(z-z_0\) by \(2s\) and use
\[
 2s(z-z_0)=(r^2-r_0^2)+(s^2-\sigma_0^2)
                    -(u^2-u_0^2)-2z_0(s-\sigma_0).
\]
Its numerator is bounded by
\(\delta(4r_0+2\sigma_0+2u_0+3\delta)\);
\(|2s|\ge3\sigma_0/2\) gives the displayed constant \(C_z\).
Since \(r_0^2=z_0^2\), subtract these squares in \(w\) to obtain
the second bound, using \(\delta\le1\).

Thus the explicit choice
\[
 0<\delta\le\min(1,\sigma_0/4,h/4,h/(4C_z),h^2/(4C_w))           \tag{B11}
\]
maps the distance polydisc into the invariant \(w,z,s\) domain, and
\(G(w,z,s)\) is the desired holomorphic distance extension, bounded by
\(M\). This includes all three collinear faces, not merely the segment
between the two particles. No division by the triangle area was made.

At a noncollinear center \(w_0=r_0^2-z_0^2>0\), use instead the planar
representative \(x_1=(\sqrt{w_0},0,z_0)\), \(x_2=\sigma_0e_3\).
Suppose the Cartesian function is holomorphic with radius \(h\) and bound
\(M\) about that representative. The estimates
\[
 |z-z_0|\le C_z\delta,\qquad |w-w_0|\le C_w\delta
\]
hold with the same constants, because \(|z_0|\le r_0\). Choose
\[
 0<\delta\le\min\left(1,\sigma_0/4,h/4,h/(4C_z),
                  w_0/(4C_w),h\sqrt{w_0}/(4C_w)\right).          \tag{B12}
\]
The positive branch of \(\sqrt w\) then exists, and
\[
 |\sqrt w-\sqrt{w_0}|
       \le |w-w_0|/\sqrt{w_0}\le h/4.
\]
Substitution of \((\sqrt w,0,z,se_3)\) into the Cartesian function supplies
the holomorphic extension, still bounded by \(M\).
Here division by \(\sqrt{w_0}\) is restricted to strictly noncollinear
charts. A uniform compact interior region must retain a positive lower
bound on \(w_0\); the collinear charts cover the missing boundary.

Every distance extension on radius \(\delta\), bounded by \(M_{\rm loc}\),
has on its half polydisc the explicit derivative bound
\[
 |\partial^\eta\mathcal U|
      \le M_{\rm loc}\eta!(2/\delta)^{|\eta|}.                     \tag{B13}
\]
All boundary C2 derivatives are restrictions of these holomorphic
derivatives. They are not defined by differentiating a singular planar
square root on a collinear face.

## 6. Exact gluing theorem in three ambient variables

Let \(K\) be any convex subset of the closed nonnegative octant in
\(\mathbb R^3\). For each \(x\in K\), let \(F_x\) be holomorphic on a
complex sup-norm polydisc \(D(x,h_x)\), \(h_x>0\). Assume a common physical
function \(f\) is defined on \(O=(0,\infty)^3\), and that
\[
 F_x=f\quad\hbox{on }D(x,h_x)\cap O.                              \tag{B14}
\]
The equality is on the full real ambient intersection. Then these
functions glue uniquely to a holomorphic function on their union.
If every \(|F_x|\le M\), the glued function has the same bound \(M\).

To prove agreement on an overlap, write \(x,y\) for the two real centers
and \(r,s\) for their radii. A nonempty complex overlap implies
\[
 |x-y|_\infty<r+s.
\]
The radius-weighted real point
\[
 p={s x+r y\over r+s}
\]
lies in \(K\) by convexity and satisfies
\[
 |p-x|_\infty={r\over r+s}|x-y|_\infty<r,\quad
 |p-y|_\infty={s\over r+s}|x-y|_\infty<s.
\]
It therefore has an open real neighborhood inside the overlap. Since
\(p\) is in the closed octant, this neighborhood meets \(O\) in a nonempty
real open set. On that set the two functions agree by (B14). The difference
has zero Taylor coefficients there (real derivatives of a holomorphic
function determine its complex Taylor coefficients), hence vanishes on
a complex neighborhood. The entire overlap is convex and connected, so
the holomorphic identity theorem gives agreement throughout it.
This proves the gluing assertion even on overlap portions outside the
physical region.

For a common radius \(h\), the union is exactly
\[
 \{z\in\mathbb C^3:\inf_{x\in K}|z-x|_\infty<h\}.                 \tag{B15}
\]
In particular, one obtains one bounded holomorphic function on a genuine
complex neighborhood of the normalized set.

If (B14) were replaced by equality only on \(K=\{a+b+c=1\}\), the assertion
would be false: the nonzero holomorphic polynomial \(a+b+c-1\) vanishes
there. The full-dimensional radial physical neighborhoods in (B14) are
therefore essential.

## 7. Finite covers and the exact conditional output

Suppose the actual physical function admits the Cartesian analytic data
used in Sections 3–5 at every normalized configuration, with retained
neighborhoods, uniformly over the parameter family under consideration.
The four types cover the nonzero closed physical octant: the three isolated
pair axes, noncollision collinear faces, and noncollinear interior.
The origin is excluded from the normalized compact set.

Each local distance polydisc of radius \(\delta_i\) gives a perimetric
polydisc of radius \(\delta_i/2\), because (B1) moves each distance by at
most twice the perimetric sup displacement. Take chart cores of half
these perimetric radii. Compactness gives a finite subcover of \(K\).
If the full perimetric chart radii are \(r_i\), choose
\[
 h=\min_i r_i/4>0.
\]
For any center \(x\in K\), a core containing \(x\) has
\(D(x,h)\subset D(x_i,r_i)\). Restrict its holomorphic extension to this
new polydisc. Its equality with the physical function still holds on the
full intersection with \(O\). Taking the maximum of the finitely many
local bounds and applying Section 6 gives (B15), with that common bound.

For a family of actual unscaled differences \(u_\varepsilon-a_0\) whose
Cartesian chart amplitudes are \(M_i\varepsilon\), every construction is
linear in those amplitudes. The resulting common complex neighborhood has
bound \(M_*\varepsilon\), independently of \(\varepsilon\) in the declared
scale interval. The preceding H12/factorial/descent work supplies the pair
chart component of these hypotheses. Uniform nonsingular Cartesian
analytic bounds, the physical rotation and Lipschitz inputs and the actual
physical solution remain explicit dependencies.

This is a conditional paper implication from stated Cartesian data to
compatible distance/perimetric analytic germs. It is not a formal discharge
of physical G1, the global approximation theorem or any spectral claim.

## 8. Provenance and review

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The frozen target is rwa_proof/RWA_THEOREM.md section 5, SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
The new quantitative KS dependency is KS_QUANTITATIVE_DESCENT_v1.md,
SHA-256 17d55abbbfafae45ae5b62e1ed0c70603a50e22f62e520dd741d970129ebc69f.

An independent child agent checked the abstract SO(2) and convex-overlap
lemmas before this text was completed. Its review specifically confirmed
the full real-dimensional equality requirement and the restricted
\(|x^2+y^2|<h^2\) domain. The coordinate inequalities and final exact
statement remain subject to a separate final review.

All work is new; frozen and sealed artifacts were preserved. There is no
identified counterexample to the inherited boundary conclusion when its
full real-neighborhood hypotheses are used.
