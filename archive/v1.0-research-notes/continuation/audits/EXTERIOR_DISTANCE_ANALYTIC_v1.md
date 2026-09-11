> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exterior distance analyticity with inverse-linear radii

Evidence category: **paper theorem**, not Lean verification. This proves
the precise local-germ conclusion called G2 in the new endpoint
approximation theorem, from an actual bounded rotationally invariant
weak Coulomb solution. It does not assume an analytic exterior estimate,
binding, a spectral gap, exponential decay, or a normalized eigenfunction.

The geometric point is to use the shortest physical separation as the
transverse coordinate. Using the total radius in every intermediate
bound can lose extra powers near a collinear triangle. The explicit
cover below avoids that loss.

## 1. Actual inputs and output

Let \(Z\ge0\), \(E\in\mathbb R\), and let
\(\psi\in L^\infty(\mathbb R^6;\mathbb R)\), with essential bound \(M_\psi\),
solve in distributions
\[
 \left[-\tfrac12(\Delta_{x_1}+\Delta_{x_2})
 -{Z\over|x_1|}-{Z\over|x_2|}+{1\over|x_1-x_2|}-E\right]\psi=0.  \tag{X1}
\]
Assume simultaneous \(SO(3)\) invariance as an L-infinity equivalence
class. Let
\[
 r=|x_1|,\quad s=|x_2|,\quad u=|x_1-x_2|,\quad
 r=b+c,\ s=a+c,\ u=a+b,\quad T=a+b+c,\quad S=r+s=a+b+2c.
\]
Here \(S\) is exactly the physical weight of the frozen theorem and
dictionary; \(T\) is an auxiliary perimetric sum.

For every fixed \(d_*>0\) there exist explicit constants \(H>0\) and
\(C_\infty<\infty\), depending only on \(Z,|E|,d_*\), such that every
real point \(x=(a,b,c)\ge0\) with \(S(x)\ge d_*\) has a holomorphic
distance germ on
\[
 D\left(x,{H\over1+S(x)}\right),\qquad
 |\widehat\psi_{\mathbb C}|\le C_\infty M_\psi.                  \tag{X2}
\]
These germs are compatible on all overlaps, including complex overlap
portions outside the physical octant. They agree with the actual
physical solution on their full real physical open intersections.
Consequently they have the Cauchy derivative bounds, at every center,
\[
 |\partial^\eta\widehat\psi(x)|
 \le C_\infty M_\psi\,\eta!
             \left({1+S(x)\over H}\right)^{|\eta|}.              \tag{X3}
\]
The boundary values and derivatives are the canonical analytic
continuations, not arbitrary representatives on measure-zero sets.

Off the physical collision sets, finite weak elliptic bootstrap gives
the ordinary smooth representative of \(\psi\). Its essential bound is
then a pointwise bound. For each fixed rotation, equality almost
everywhere between smooth representatives implies equality everywhere
on that open set. This defines the scalar reduced function on the
full real open octant. The construction below also supplies its
continuous physical extension across each isolated pair collision.
It asserts no regularity at the simultaneous collision, which is
excluded by \(S\ge d_*\).

## 2. Uniform unscaled collision charts, including distant spectators

Put \(d_0=d_*/4\) and
\[
 h_0=\min\left({1\over32},{d_0\over64\sqrt3},
                              \sqrt{d_0\over64\sqrt3}\right).
\]
For every real \(\sigma\ge d_0\), use the complex polydisc
\(|y|_\infty<h_0\), \(|t-\sigma e_3|_\infty<h_0\).
Write \(\varrho(y)=\sum_{i=1}^4y_i^2\) and use the actual KS polynomial.
The elementary complex estimates are
\[
 |\varrho|\le4h_0^2,\quad
 \|t-\sigma e_3\|_2\le d_0/64,\quad
 \|K(y)\|_2\le4\sqrt3h_0^2\le d_0/16.                          \tag{X4}
\]
Thus \(t\), \(K(y)-t\), and \(t\pm K(y)/2\), at their corresponding
real centers of length \(\sigma\), have displacements less than
\(d_0/8\). The reciprocal-distance branch theorem gives positive-real
holomorphic branches on this entire domain, each bounded by \(2/d_0\).
The formula uses the holomorphic polynomial squared distance, never a
Hermitian norm as a complex function.

The actual unscaled weak lift has zero source. Its two operators are
\(P_4+B_{\rm nuc}\) and \(P_1+B_{\rm pair}\), with
\[
 \begin{split}
 B_{\rm nuc}&=-8Z+8\varrho(-Z R(t)+R(K(y)-t))-8E\varrho,\\
 B_{\rm pair}&=4-4Z\varrho(R(t+K(y)/2)+R(t-K(y)/2))-4E\varrho.
 \end{split}                                                   \tag{X5}
\]
They have respective complex bounds
\[
 M_{\rm nuc}=8Z+{64h_0^2(Z+1)\over d_0}+32h_0^2|E|,\qquad
 M_{\rm pair}=4+{64Zh_0^2\over d_0}+16h_0^2|E|.                 \tag{X6}
\]
On the real half boxes their derivatives are bounded by
\(M_j(2/h_0)^k k!\). These constants do not depend on \(\sigma\).

The pullback is initially defined using the smooth representative away
from \(y=0\), and may be assigned any bounded values on that zero-measure
set. It has L-infinity bound \(M_\psi\). The codimension-four L2
removability theorem supplies the full weak equation across \(y=0\).
Thus no value of an arbitrary representative on a collision set enters
the weak argument. H12 initialization and the factorial theorem then
produce its canonical analytic representative.

For explicit constants, evaluate the H12 lemma with outer half-width
\(h_0/2\), target half-width \(h_0/4\), \(c_j=4,1\), coefficient
data \(b_0=M_j\), \(K_{11}=M_j(2/h_0)^{11}11!\), zero source, and
spacing \(h_0/136\). If \(A_{y,j},A_{t,j}\) are its displayed constants,
its H12 bound is \(H_jM_\psi\), where
\[
 H_j=\sqrt{50388}\,A_{y,j}^5A_{t,j}^{12}h_0^{7/2}.
\]
Evaluate the factorial theorem with \(a=b=h_0/4,\rho=h_0/8\),
\(M=\max(1,M_j)\), \(A=2/h_0\), and zero source. In its constants
\(W=1\) and \(S\le498H_jM_\psi\). Denote its final constants by
\(C_{*,j},A_{*,j}\), and set
\[
 r_K=\min(h_0/16,(28\max_j A_{*,j})^{-1},1),\quad
 M_K=\max_j(996C_{*,j}H_j),\quad D_K=32r_K^{-2},\quad
 h_A=\min((2D_K)^{-1},r_K/2).
\]
Constructive KS descent therefore has half-polyradius coefficient
bounds \(16M_KM_\psi\) and \(16D_KM_KM_\psi\).
The physical rotation invariance and decomposition uniqueness give
the separate SO(2) invariance required by the boundary-coordinate lemma.

Set
\[
 \delta_A=\min(1,d_0/16,h_A/24),\qquad \kappa=\delta_A/4.         \tag{X7}
\]
That lemma supplies distance germs of radius \(\delta_A\), and
perimetric germs of radius \(2\kappa\), at every nuclear or pair axis
center with \(\sigma\ge d_0\). Their bound is
\(17M_KM_\psi\), since \(\delta_AD_K\le1/48\).
No electron-exchange symmetry is assumed; the second nuclear chart
is the same argument applied to the exchanged function.

For a perimetric point \(x\) with \(S\ge d_*\), its auxiliary sum
\(T\ge d_*/2\). Projection to the appropriate axis point
\((T,0,0)\), \((0,T,0)\), or \((0,0,T)\) has sup distance equal
to the respective physical separation. Thus all points with
\[
 \ell:=\min(r,s,u)<\kappa                                      \tag{X8}
\]
are in these uniform axis cores. Their axis centers satisfy the
declared \(\sigma\ge d_0\).

## 3. Uniform nonsingular Cartesian germs

Let \(d_{\rm sep}=\kappa/2\), \(R_C=d_{\rm sep}/(16\sqrt3)\), and
\[
 M_b=4(2Z+1)/d_{\rm sep}+2|E|,\quad M=\max(1,M_b),\quad
 A=\max(1,2/R_C).
\]
At every real configuration with separations at least \(d_{\rm sep}\),
the actual equation is \((-\Delta+B)\psi=0\), with \(B=2V-2E\).
The coefficient theorem gives these uniform analytic bounds on the
half box of the complex radius-\(R_C\) polydisc. Its real outer
L2 norm is at most \(M_\psi R_C^3\), independent of the center.

Evaluate the nonsingular elliptic theorem in dimension six with
\(a=R_C/4,e_0=R_C/16,\rho=R_C/8,M,A\) as above and zero source.
Let \(A_1,C_{*,C},A_{*,C}\) be its constants. Set
\[
 h_C=\min(R_C/16,(24A_{*,C})^{-1},1),\quad
 M_C=56C_{*,C}A_1R_C^3,\quad h_F=h_C/2.                         \tag{X9}
\]
The actual Cartesian solution is holomorphic with bound \(M_CM_\psi\)
on each radius-\(h_C\) polydisc. The factor 56 is \(2J_6\), with
\(J_6=28\).

The same bound holds on radius-\(h_F\) polydiscs in the coordinates
\((X,t)=(x_1,x_2)\), their exchanged version, or
\((X,t)=(x_1-x_2,(x_1+x_2)/2)\). For the pair coordinates, each
physical complex displacement is at most
\(|\Delta t|_\infty+|\Delta X|_\infty/2<3h_C/4\).
Real rotations of the frame preserve the equation, the potential
separation bounds and the global solution bound. Thus this constant
also applies to every planar representative used below.

## 4. Distance maps in the shortest-separation coordinates

At a nonsingular real center choose \(X\) to have length
\(\ell=\min(r,s,u)\). If \(\ell=r\) or \(s\), use the nuclear coordinates,
exchanging labels if needed, and write \(t=\tau_0e_3\) with
\(\tau_0=s\ge S/2\). In a planar representative write
\[
 X=(\sqrt{w_0},0,z_0),\qquad |z_0|\le\ell,\quad
 z={r^2+s^2-u^2\over2s},\quad \tau=s,\quad w=r^2-z^2.
\]
The boundary lemma's estimates give
\[
 |\tau-\tau_0|\le\delta,\quad |z-z_0|\le16\delta,\quad
 |w-w_0|\le(34\ell+257)\delta                                  \tag{X10}
\]
whenever all three distance displacements have modulus at most
\(\delta\le\min(1,S/100)\). Indeed
\(L_0=r+s+u\le2S\) and \(s\ge S/2\), so \(C_z\le16\).

If \(\ell=u\), use relative and center coordinates. Then
\[
 q=(r^2+s^2)/2-u^2/4,\quad \tau=\sqrt q,\quad
 z={r^2-s^2\over2\tau},\quad w=u^2-z^2.                         \tag{X11}
\]
At the real center, \(u\le\min(r,s)\le S/2\), and the triangle
inequality \(|r-s|\le u\) gives
\[
 S/3\le\sqrt3S/4\le\tau_0\le S/2.                              \tag{X12}
\]
For complex distance displacement at most
\(\delta\le\min(1,S/100)\),
\[
 |q-q_0|
 \le(S+u/2)\delta+5\delta^2/4
 \le2S\delta<\tau_0^2/4.
\]
The positive branch therefore exists on the entire polydisc.
It satisfies
\[
 |\tau|\ge S/6,\qquad |\tau-\tau_0|\le6\delta.
\]
Subtract \(2\tau z_0\) in the numerator of \(z\). Since
\(|z_0|\le u=\ell\le S/2\), its difference is at most
\((2S+12\ell)\delta+2\delta^2<9S\delta\).
Division by \(|2\tau|\ge S/3\) yields
\(|z-z_0|\le27\delta\le32\delta\). It follows that
\[
 |w-w_0|\le(66\ell+1025)\delta
                  \le2048(1+\ell)\delta.                     \tag{X13}
\]

Consequently both choices obey the one uniform collection
\[
 |\tau-\tau_0|\le6\delta,\qquad |z-z_0|\le32\delta,\qquad
 |w-w_0|\le2048(1+\ell)\delta.                                 \tag{X14}
\]
These are estimates around real centers. They do not assert a
comparison of ordered complex distances. The scale \(1+\ell\)
appears only in the squared-height estimate; the coordinate \(z\)
and spectator length have bounded sensitivity independent of \(S\).

## 5. Collinear radii and an exact geometric lower bound

Define
\[
 A_C=\min(1,\kappa/200,h_F/24,h_F/128,h_F^2/8192),\qquad
 \gamma=\min(\kappa/16,A_C/32,1/32).                            \tag{X15}
\]
At every noncollision collinear center of minimum separation
\(\ell_q\ge\kappa/2\), (X14) shows that the distance polydisc of radius
\[
 \delta_q={A_C\over1+\ell_q}
\]
maps strictly into the SO(2) invariant-series domain
\(|w|<h_F^2, |z-z_0|,|\tau-\tau_0|<h_F\).
Specifically these displacements are at most
\(h_F^2/4,h_F/4,h_F/4\).
The hypothesis \(\delta_q\le S(q)/100\) holds because
\(S(q)\ge2\ell_q\ge\kappa\).
Thus a holomorphic distance germ exists with bound \(M_CM_\psi\).
Its perimetric radius is \(A_C/[2(1+\ell_q)]\).

Let \(m=\min(a,b,c)\). Sort the three perimetric coordinates as
\(m\le v\le w\). Then
\[
 \ell=m+v,\quad v\ge\ell/2,\quad w\ge T/3,\quad
 abc\ge m\ell T/6.                                            \tag{X16}
\]
Heron's formula is \(\mathrm{Area}^2=Tabc\). In either chosen coordinate
system, \(|X\times t|=|x_1\times x_2|\). The spectator length is
at most \(T\): this is immediate for a nuclear spectator, while
for a pair spectator \(\tau_0\le S/2\le T\). Therefore
\[
 w_0={|X\times t|^2\over|t|^2}
     ={4Tabc\over|t|^2}\ge{4abc\over T}
     \ge {2\over3}m\ell.                                      \tag{X17}
\]
This lower bound is the key to an exterior estimate with just one
power of the total radius.

Consider a point with \(\ell\ge\kappa\). If
\[
 m<{\gamma\over1+\ell},
\]
set a minimizing perimetric coordinate to zero and transfer its
value to another coordinate. The boundary point \(q\) has the same
\(T\), displacement \(|q-x|_\infty=m\), and
\[
 \ell_q\ge\ell-2m\ge7\kappa/8>\kappa/2,\quad
 1+\ell_q\le1+\ell+2\gamma<2(1+\ell).
\]
It is thus a nonsingular collinear point whose perimetric germ has
radius at least \(A_C/[4(1+\ell)]\). Its center-to-\(x\) displacement
is at most \(A_C/[32(1+\ell)]\).

In the remaining region, (X17) yields the positive constant
\[
 w_0\ge w_*:={2\gamma\over3}\,{\kappa\over1+\kappa}>0.           \tag{X18}
\]
Define
\[
 A_I=\min(A_C,w_*/8192,h_F\sqrt{w_*}/8192).
\]
On the distance polydisc of radius \(A_I/(1+\ell)\), (X14) gives
\[
 |w-w_0|\le w_*/4\le w_0/4,\qquad
 |\sqrt w-\sqrt{w_0}|
 \le {|w-w_0|\over\sqrt{w_0}}\le h_F/4.
\]
Here the square root has the positive real-center branch.
Substitution of \((\sqrt w,0,z,\tau e_3)\) into the actual Cartesian
analytic germ is valid by (X14), and gives a distance germ with
bound \(M_CM_\psi\). Its perimetric radius is
\(A_I/[2(1+\ell)]\). The square root is not differentiated at
zero; zero height was covered by the SO(2) series.

## 6. Recentered physical germs and global compatibility

Take
\[
 H=\min(\kappa/2,A_C/32,A_I/4),\qquad
 C_\infty=\max(17M_K,M_C).                                     \tag{X19}
\]
Every point with \(S\ge d_*\) has a germ on the polydisc in (X2).
For axis-core points its center-to-axis displacement is less than
\(\kappa\), and its added radius is at most \(H\le\kappa/2\),
within the full axis radius \(2\kappa\).
For face-core points, the displacement and added radius are each at
most \(A_C/[32(1+\ell)]\), because \(\ell\le S\). Their sum is
strictly smaller than the full radius \(A_C/[4(1+\ell)]\).
For the remaining interior points,
\(H/(1+S)\le A_I/[4(1+\ell)]\), which retains half of the supplied
perimetric radius.

Every recentered germ agrees with the same physical reduced function
on the full real open octant in its domain. The center set
\[
 K_{d_*}=\{a,b,c\ge0:a+b+2c\ge d_*\}
\]
is convex, although unbounded. Apply the convex-overlap gluing theorem
with the now variable radii \(H/(1+S(x))\). Its proof requires neither
compactness nor equal radii: the radius-weighted real point between two
centers is still in \(K_{d_*}\) and in both open polydiscs.
A nearby full-dimensional real physical open set forces equality.
This proves compatibility throughout the complex overlaps and preserves
the uniform bound. Cauchy's formula proves (X3).

All constants are finite explicit formulas in the stated physical
parameters and the displayed constants of the component lemmas.
No behavior of \(\psi\) at infinity, except the stated boundedness,
has entered the proof. This is precisely a G2 implication from
actual weak-solution and symmetry data, and supplies no exponential
H2 tail estimate or approximation algorithm by itself.

## 7. Provenance and review scope

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The frozen target is the exterior-coordinate argument in
rwa_proof/GLOBAL_DYADIC_ATTEMPT.md, SHA-256
b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
The explicit new target is G2 in ENDPOINT_ONE_THIRD_v3.md, SHA-256
cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a.

New local paper dependencies:

| Artifact | SHA-256 |
|---|---|
| KS_WEAK_REMOVABILITY_v1.md | ba8769955d76e01ce561a68071ad5832828106c3ca614ea8fe1e19c36aa78cde |
| GRUSHIN_H12_WEAK_INITIALIZATION_v1.md | ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812 |
| GRUSHIN_FACTORIAL_RECURRENCE_v1.md | 5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594 |
| KS_QUANTITATIVE_DESCENT_v1.md | 17d55abbbfafae45ae5b62e1ed0c70603a50e22f62e520dd741d970129ebc69f |
| NONSINGULAR_ELLIPTIC_FACTORIAL_v1.md | d776fd6de1ea4df30b5bbddfa0197d3d68c32b84514b9c5ccaaaebfb0d07feb0 |
| DISTANCE_BOUNDARY_GERMS_v1.md | b956af4f732085ae83eb9ace3a965a59ca18bd85e922178f3453f58748c86991 |
| COULOMB_COMPLEX_COEFFICIENT_BOUNDS_v1.md | a6b9361f229a29e3df2cf0e3e20552da7cfeb49dfbbf7f8f15d0112375eaa5b5 |

The coefficient branch estimate is used at its actual real center with
its declared perturbation radius; no complex Euclidean norm is treated
as holomorphic. The auxiliary finite checker records rational identities
and geometric inequalities. It does not verify the infinite analytic
claims. This manuscript remains subject to separate independent review.
Frozen and sealed successful artifacts were preserved.
