> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Uniform local distance analyticity for an actual Coulomb solution

Evidence category: **paper theorem**. The hypothesis is an actual scalar,
locally Lipschitz, rotationally invariant distributional solution of the
two-electron Coulomb equation. The conclusion supplies its compatible
complex distance germs with a uniform scale and amplitude. No analytic
germ or derivative estimate is assumed. Existence and the stated symmetry
of a physical ground state remain separate obligations.

The proof composes the new weak KS, initialization, all-order, constructive
descent, nonsingular elliptic and boundary-coordinate lemmas. It gives an
explicit geometric cover, avoiding an unspecified compactness selection.
None of these analytic assertions is claimed to be Lean-verified.

## 1. Exact actual-solution theorem

Fix \(Z\ge0\), \(E\in\mathbb R\), and \(R_{\rm phys}>0\). Suppose that a
real function \(\psi\) is Lipschitz with constant \(L\ge0\) on the open
Euclidean ball \(B_{R_{\rm phys}}(0)\subset\mathbb R^6\), and that
\[
 \left[-\tfrac12(\Delta_{x_1}+\Delta_{x_2})
 -{Z\over|x_1|}-{Z\over|x_2|}+{1\over|x_1-x_2|}-E\right]\psi=0
                                                                  \tag{P1}
\]
there in distributions. All products in (P1) are ordinary locally
integrable functions. Assume simultaneous rotation invariance:
\[
 \psi(Ux_1,Ux_2)=\psi(x_1,x_2)\qquad(U\in SO(3)).                 \tag{P2}
\]
Set
\[
 a_0=\psi(0),\qquad \Lambda=L+|a_0|,\qquad
 \bar\varepsilon=\min(1,R_{\rm phys}/4).
\]
Use \(a,b,c\) for perimetric variables and \(S=a+b+c\), with
\[
 r=b+c,\qquad s=a+c,\qquad u=a+b,\qquad
 K=\{a,b,c\ge0:S=1\}.
\]
Here \(S\) is only the perimetric sum used to organize the cover.
The frozen theorem and dictionary use the distinct physical weight
\(S_{\rm phys}=r+s=a+b+2c\). Their exact comparison and conversion
are given in Section 7; the Hamiltonian and trial dictionary are unchanged.
For positive real \(a,b,c\), choose any two vectors with distances
\((r,s,u)\), and define, whenever their scaled positions are in the ball,
\[
 f_\varepsilon(a,b,c)
   =\psi(\varepsilon x_1,\varepsilon x_2)-a_0.                    \tag{P3}
\]
This is well-defined: equal distance triples give equal Gram matrices,
and an isometry between the spans of two ordered vector pairs extends
to an element of \(SO(3)\). A possible orientation reversal is corrected
on their nontrivial orthogonal complement. The same argument covers
collinear and zero-vector pairs.

There are explicitly specified \(h>0\) and \(C<\infty\), depending only on
\(Z,|E|,\bar\varepsilon\), such that, for every
\(0<\varepsilon\le\bar\varepsilon\), \(f_\varepsilon\) has a unique
holomorphic extension \(F_\varepsilon\) to
\[
 K_h=\{z\in\mathbb C^3:\inf_{x\in K}|z-x|_\infty<h\},
 \qquad |F_\varepsilon|\le C\Lambda\varepsilon.                  \tag{P4}
\]
The equality with (P3) is on the full real physical intersection,
including a radial neighborhood of \(S=1\). No holomorphic dependence
on \(\varepsilon\) is asserted. At every \(x\in K\),
\[
 |\partial^\eta F_\varepsilon(x)|
 \le C\Lambda\varepsilon\,\eta!\,h^{-|\eta|};                    \tag{P5}
\]
on \(K_{h/2}\) the bound with \(2/h\) holds. These derivatives give the
actual limiting physical derivatives at every collision and collinear
boundary point of the normalized distance region.

The solution is scalar. There is no assumption of electron-exchange
symmetry and no conclusion about a unique fermionic spin eigenvector.
Equation (P1) has precisely the physical kinetic factor \(1/2\) and
repulsive electron-pair sign.

## 2. Fixed collision-chart constants and the weak input

Here and below, evaluating the explicit constants of a cited new lemma
is part of the definition of a constant; no norm of an unknown derivative
of \(\psi\) is used. Write \(h_0=1/32\). For each \(j\in\{\mathrm{nuc},
\mathrm{pair}\}\), use \(c_j=4,1\), respectively, and
\[
 M_{\mathrm{nuc}}=8Z+(Z+1)/16+\bar\varepsilon|E|/32,\qquad
 M_{\mathrm{pair}}=4+Z/16+\bar\varepsilon|E|/64.                  \tag{P6}
\]
The coefficient theorem proves the complex branches on the box of
half-width \(h_0\), and on its real half box
\[
 |D^\eta b_{\varepsilon,j}|
 \le M_j64^{|\eta|}|\eta|!,\qquad B_{\varepsilon,j}
 =\varepsilon b_{\varepsilon,j}.                               \tag{P7}
\]
The centers are \(y=0,t=e_3\). The actual normalized difference is
\[
 v_{\varepsilon,j}
   ={u_{\varepsilon,j}-a_0\over\varepsilon},
 \qquad(P_{c_j}+B_{\varepsilon,j})v_{\varepsilon,j}
        =-a_0b_{\varepsilon,j}.                                \tag{P8}
\]
For the nuclear chart \(u_\varepsilon=\psi(\varepsilon K(y),
\varepsilon t)\); for the pair chart
\(u_\varepsilon=\psi(\varepsilon(t+K(y)/2),
\varepsilon(t-K(y)/2))\).

This is a full distributional equation across \(y=0\). Indeed (P1) and
the nonsingular weak elliptic bootstrap imply ordinary smoothness away
from the physical collision. The explicit KS identity gives (P8)
off \(y=0\). The actual pullback is bounded, and the codimension-four
L2 removability theorem gives the full weak equation. No chain rule
at a degenerate map or pre-existing analytic regularity is assumed.
All real scaled images of the half boxes have norm less than
\(2\varepsilon\le R_{\rm phys}/2\), by the coefficient theorem.
Consequently
\[
 |v_{\varepsilon,j}|\le2L.                                    \tag{P9}
\]

Apply H12 weak initialization with outer half-width \(h_0/2\) in all
seven variables and target half-width \(h_0/4\). Its 34-gap spacing is
\(\delta_H=h_0/136\). In its H3/H4 constants substitute
\[
 b_0=\bar\varepsilon M_j,\quad
 K_{11}=\bar\varepsilon M_j64^{11}11!,\quad c=c_j,\quad R=h_0.
\]
Writing its resulting constants as \(A_{y,j},A_{t,j}\), set
\[
 H_j=\sqrt{50388}\,A_{y,j}^{5}A_{t,j}^{12}
             (2+M_j64^{11}11!)h_0^{7/2}.                       \tag{P10}
\]
The outer L2 norm is at most \(2Lh_0^{7/2}\), and every source
derivative through order eleven is bounded by
\(|a_0|M_j64^{11}11!h_0^{7/2}\). Therefore the actual \(v_{\varepsilon,j}\)
has H12 norm at most \(H_j\Lambda\) on the target box.

## 3. All orders, descent, and fixed vertex cores

Apply the factorial theorem on the box with \(a=b=h_0/4\),
\(\rho=h_0/8\), \(c=c_j\), and analytic coefficient constants
\[
 M=\max(1,\bar\varepsilon M_j),\quad A=64.
\]
The source prefactor may be taken to be
\(F_j=|a_0|M_j(h_0/2)^{7/2}\).
The quantity \(W\) in that theorem is one here. Thus its \(S\) is at most
\[
 S_j\Lambda,\qquad S_j=M_j(h_0/2)^{7/2}+498H_j.
\]
Let \(C_{*,j},A_{*,j}\) be its R1 constants, evaluated with these data, and
define
\[
 r_K=\min\left(h_0/16,{1\over28\max_j A_{*,j}},1\right),\qquad
 M_K=\max_j(2C_{*,j}S_j),\qquad D_K=32r_K^{-2}.                  \tag{P11}
\]
At the chart center the factorial Taylor series converges on the complex
seven-variable sup polydisc of radius \(r_K\), agrees with the actual
real solution there, and is bounded by \(M_K\Lambda\). Indeed the
sum-norm Taylor factor is at most \(7A_{*,j}r_K\le1/4\), and the
real polydisc lies inside the retained real half-width \(h_0/8\).

The real lift is KS-circle invariant because it is an actual pullback.
Constructive coefficient descent with \(M_y=M_s=r_K^{-1}\) gives
the actual normalized difference in the form \(A(X,t)+|X|B(X,t)\).
On the half polyradii its analytic coefficients are bounded by
\[
 16M_K\Lambda,\qquad16D_KM_K\Lambda.
\]
Put
\[
 h_A=\min((2D_K)^{-1},r_K/2),\qquad
 \delta_V=\min(1/16,h_A/24),\qquad \kappa=\delta_V/4.             \tag{P12}
\]
The nuclear and pair boundary-coordinate lemmas with \(\sigma_0=1\)
both apply with Cartesian radius \(h_A\). Their distance polydiscs
have radius \(\delta_V\). The bound is at most
\[
 16M_K(1+\delta_VD_K)\Lambda\le17M_K\Lambda,                     \tag{P13}
\]
since \(\delta_VD_K\le1/48\).
Multiplication by \(\varepsilon\) restores the unnormalized
difference \(f_\varepsilon\).

Separate-coefficient SO(2) invariance follows from (P2) and uniqueness
of analytic-plus-distance decomposition. That uniqueness is the
direct descent theorem's real two-sided line argument. Electron
exchange supplies the other nuclear chart by applying the same proof
to the exchanged function; it does not assume that \(\psi\) itself
is exchange symmetric.

Each vertex therefore has a perimetric germ of radius
\(\delta_V/2=2\kappa\), bound \(17M_K\Lambda\varepsilon\), and equality
with the physical function on the full real physical intersection.
For \(x=(a,b,c)\in K\),
\[
 |x-(1,0,0)|_\infty=b+c=r,                                    \tag{P14}
\]
and the two analogous distances are \(s\) and \(u\). Thus points
with \(\min(r,s,u)<\kappa\) lie in the cores of these fixed germs.

## 4. One uniform nonsingular Cartesian estimate

Fix \(d=\kappa/2>0\), and put
\[
 R_C=d/(16\sqrt3),\qquad M_b=4(2Z+1)/d+2\bar\varepsilon|E|.
\]
At every normalized real configuration whose three separations are
at least \(d\), the coefficient theorem gives an analytic extension
on the Cartesian polydisc of radius \(R_C\), and bounds on its
half box with constants
\[
 M=\max(1,\bar\varepsilon M_b),\qquad A=\max(1,2/R_C).
\]
The actual normalized difference
\(v_\varepsilon(X)=(\psi(\varepsilon X)-a_0)/\varepsilon\)
satisfies
\[
 (-\Delta_X+B_\varepsilon)v_\varepsilon
       =-a_0B_\varepsilon/\varepsilon,\quad
 B_\varepsilon=2\varepsilon V(X)-2\varepsilon^2 E.              \tag{P15}
\]
Its outer L2 norm is at most \(2LR_C^3\), and the analytic source
prefactor is at most \(|a_0|M_bR_C^3\).

Evaluate the nonsingular elliptic theorem with \(d_{\rm dim}=6\),
\(a=R_C/4\), \(e_0=R_C/16\), \(\rho=R_C/8\), and the above \(M,A\).
The notation \(d_{\rm dim}\) distinguishes spatial dimension from
the separation \(d\). Denote its initialization constant by \(A_1\),
its number of norm terms by \(J_6=28\), and its final constants by
\(C_{*,C},A_{*,C}\). Set
\[
 S_C=R_C^3\{M_b+J_6A_1(2+M_b)\},\quad
 h_C=\min(R_C/16,(24A_{*,C})^{-1},1),\quad
 M_C=2C_{*,C}S_C.                                              \tag{P16}
\]
Its norm input \(S\) is at most \(S_C\Lambda\), so the actual
normalized difference is holomorphic with bound \(M_C\Lambda\)
on the Cartesian polydisc of radius \(h_C\) about every such center.
The six-variable Taylor sum-norm factor is at most \(1/4\).
These constants are independent of the center and scale.

All configurations in this application are normalized, hence
\(|X_1|,|X_2|\le1\). The physical ball containment of the coefficient
theorem therefore applies, including after changing the real orthogonal
frame. The Coulomb equation and Lipschitz norm are rotation invariant.

## 5. Explicit collinear cover and Heron's lower bound

Set
\[
 C_w=3+32/\kappa+256/\kappa^2,\qquad
 \delta_C=\min\left(1,\kappa/8,h_C/4,h_C\kappa/64,
                                     h_C^2/(4C_w)\right),\quad
 \gamma=\min(\kappa/8,\delta_C/8).                              \tag{P17}
\]
At a normalized noncollision collinear center with separations
at least \(d=\kappa/2\), its spectator length \(\sigma_0\ge\kappa/2\)
and \(L_0=r_0+s_0+u_0=2\). Thus the constants in the boundary lemma
obey
\[
 C_z=4L_0/\sigma_0\le16/\kappa,\qquad
 2r_0(1+C_z)+1+C_z^2\le C_w.
\]
Equation (P17) is consequently no larger than every admissible radius
in B11. A collinear distance germ of radius \(\delta_C\) exists
with bound \(M_C\Lambda\varepsilon\). Its perimetric radius is
\(\delta_C/2\).

Now take \(x=(a,b,c)\in K\) with all three separations at least \(\kappa\).
If \(m=\min(a,b,c)<\gamma\), set one minimizing coordinate to zero
and add its value to a different coordinate. This produces a boundary
point \(q\in K\) with
\[
 |q-x|_\infty=m<\gamma,\qquad
 \min(r(q),s(q),u(q))\ge\kappa-2m\ge3\kappa/4>d.                \tag{P18}
\]
Thus \(q\) is a noncollision collinear point. Its germ contains a
perimetric neighborhood of \(x\) with a fixed remaining margin,
since \(\gamma\le\delta_C/8\).

The remaining points have \(a,b,c\ge\gamma\). The physical triangle
has squared area \(Sabc=abc\) by Heron's formula. Choosing
\(x_2=se_3\), \(x_1=(\sqrt{w_0},0,z_0)\) gives
\[
 w_0={4abc\over s^2}\ge4\gamma^3>0,                            \tag{P19}
\]
because \(s\le1\). Set
\[
 \delta_I=\min\left(\delta_C,{\gamma^3\over C_w},
                             {h_C\gamma^{3/2}\over2C_w}\right).
                                                                  \tag{P20}
\]
The interior boundary-chart conditions B12 now hold: their last
two restrictions are \(w_0/(4C_w)\) and
\(h_C\sqrt{w_0}/(4C_w)\), respectively, and (P19) makes (P20)
no larger than either. The other restrictions were included in
\(\delta_C\). There is therefore a distance germ of radius
\(\delta_I\), hence perimetric radius \(\delta_I/2\), bounded by
\(M_C\Lambda\varepsilon\).

This proves coverage without dividing by a vanishing triangle area.
The inverse square root is used only in the interior with the positive
bound (P19); the separate SO(2) invariant series handles all collinear
faces. The physical pair axes were already handled by (P12).

## 6. Common radius, compatibility, and all-order output

The constants in the theorem can now be chosen to be
\[
 h=\min(1/12,\kappa/2,\delta_C/8,\delta_I/4),\qquad
 C=\max(17M_K,M_C).                                            \tag{P21}
\]
Every \(x\in K\) has a germ on \(D(x,h)\) with bound
\(C\Lambda\varepsilon\). Explicitly:

* In a vertex core, the center-to-vertex displacement is less than
  \(\kappa\), and \(h\le\kappa/2\); the full vertex radius is \(2\kappa\).
* Near a collinear face, (P18) gives displacement less than
  \(\delta_C/8\), while \(h\le\delta_C/8\); the full face radius is
  \(\delta_C/2\).
* Elsewhere, the germ centered at \(x\) has radius \(\delta_I/2\),
  and \(h\le\delta_I/4\).

All restrictions still agree with the actual function on the full real
positive-octant intersection of their new polydiscs. Because
\(h\le1/12\), every such real point has \(S<5/4<2\). Its physical
representative has norm at most \(\sqrt2S\), so its scaled position
is in \(B_{R_{\rm phys}}\) for the entire declared scale interval.
Thus there is no missing radial physical domain in this agreement.

The convex-overlap theorem for the three ambient complex variables
applies to these equal-radius germs centered on the convex set \(K\).
On every nonempty overlap, a real point in \(K\) lies strictly inside
both polydiscs; a nearby full-dimensional real physical open set
forces equality by holomorphic uniqueness. Equality just on \(S=1\)
would not suffice, and is not used. The glued function has exactly
the bound in (P4). Cauchy's formula on its contained polydiscs gives
(P5) and the half-neighborhood version. Reality on physical open sets
also gives reality of the analytic extensions on their real domains.

All parameters in (P21) are positive and finite. They are obtained
from arithmetic, factorials at fixed orders, roots, minima and maxima,
and the displayed finite formulas of the component operator lemmas.
No compact-cover selection or unknown regularity constant is concealed.
These are explicit mathematical constants, not an implementation that
can evaluate an arbitrary supplied physical solution.

## 7. Truncated shells and the actual scope of G1

Fix \(0<\alpha\le\beta<\infty\), and let
\[
 K_{\alpha,\beta}=\{a,b,c\ge0:\alpha\le S\le\beta\}.
\]
For every \(0<\varepsilon\le\bar\varepsilon/\beta\), the same actual
physical difference has a holomorphic extension to the complex
\(\alpha h\)-neighborhood of \(K_{\alpha,\beta}\), with bound
\[
 C\Lambda\beta\varepsilon.                                    \tag{P22}
\]
To prove this, at a real center \(x\) set the fixed real number
\(t=S(x)\). Then \(x/t\in K\), and define its local germ by
\[
 z\longmapsto F_{\varepsilon t}(z/t).
\]
It exists on \(D(x,th)\), contains \(D(x,\alpha h)\), has the stated
bound, and equals the physical function on its full real physical
intersection by homogeneous scaling of distances. Here \(t\) is frozen
at the center; no analytic dependence on the scale parameter is needed.
The convex-overlap argument applies because \(K_{\alpha,\beta}\) is
convex. The physical intersections have \(S<2\beta\), giving the
same physical ball containment as before.

The physical weight satisfies
\[
 S\le S_{\rm phys}=r+s=a+b+2c\le2S.                            \tag{P23}
\]
Consequently the actual fitting shell
\(\{a,b,c\ge0:1/4\le S_{\rm phys}\le2\}\) used in the endpoint
approximation theorem is contained in \(K_{1/8,2}\).
Taking \(\alpha=1/8,\beta=2\) supplies a genuine compatible complex
neighborhood of that fitting shell with radius \(h/8\) and bound
\(2C\Lambda\varepsilon\), for
\(0<\varepsilon\le\bar\varepsilon/2\). This conversion changes no
dictionary exponent or physical coordinate.

There is also a direct weighted estimate at every physical point
\(x=(a,b,c)\ne0\) with \(S_{\rm phys}(x)<\bar\varepsilon\).
Set the fixed real scale \(\varepsilon=S(x)\) and \(y=x/\varepsilon\in K\).
The identity between the physical function and
\(F_\varepsilon(z/\varepsilon)\) holds on a full local real physical
neighborhood of \(x\). Cauchy's bound (P5) therefore gives, with
\(k=|\eta|\),
\[
 |\partial^\eta(\widehat\psi-a_0)(x)|
   \le C\Lambda\,\eta!\,h^{-k}S(x)^{1-k}
   \le C\Lambda(2/h)^k k!\,S_{\rm phys}(x)^{1-k}.                \tag{P24}
\]
For \(k=0\) the last step uses \(S\le S_{\rm phys}\); for \(k\ge1\)
it uses \(S\ge S_{\rm phys}/2\). Since
\(\bar\varepsilon\le1\), the same bound with the weight
\(S_{\rm phys}^{\sigma-k}\) holds for every fixed \(0<\sigma<1\).
The compatible boundary derivatives have already been established,
so (P24) discharges the local G1 conclusion, including its actual
physical weight, under precisely the actual-solution hypotheses of
Section 1. It does not assume the desired G1 estimate as a premise.

This supplies that **local paper-level analytic premise for every actual
solution satisfying (P1)–(P2) and the stated Lipschitz hypothesis**.
It does not establish that the intended physical ground branch exists,
is Lipschitz or rotationally invariant; it does not supply exterior
decay, the required global normalization or spectral separation.
The ground-state and global G1–G3 obligations must still be connected
to the actual physical spectral problem before any full Theorem T
or its numerical procedure can be claimed.

## 8. Exact dependencies and preservation

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The precise frozen target is rwa_proof/UNIFORM_ANALYTIC_AUDIT.md,
SHA-256 5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c,
and rwa_proof/RWA_THEOREM.md sections 2–5, SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.

New local dependencies, in this audits directory:

| Paper artifact | SHA-256 |
|---|---|
| KS_WEAK_REMOVABILITY_v1.md | ba8769955d76e01ce561a68071ad5832828106c3ca614ea8fe1e19c36aa78cde |
| GRUSHIN_H12_WEAK_INITIALIZATION_v1.md | ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812 |
| GRUSHIN_FACTORIAL_RECURRENCE_v1.md | 5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594 |
| KS_QUANTITATIVE_DESCENT_v1.md | 17d55abbbfafae45ae5b62e1ed0c70603a50e22f62e520dd741d970129ebc69f |
| NONSINGULAR_ELLIPTIC_FACTORIAL_v1.md | d776fd6de1ea4df30b5bbddfa0197d3d68c32b84514b9c5ccaaaebfb0d07feb0 |
| DISTANCE_BOUNDARY_GERMS_v1.md | b956af4f732085ae83eb9ace3a965a59ca18bd85e922178f3453f58748c86991 |
| COULOMB_COMPLEX_COEFFICIENT_BOUNDS_v1.md | a6b9361f229a29e3df2cf0e3e20552da7cfeb49dfbbf7f8f15d0112375eaa5b5 |

Every component except the last coefficient theorem already has a
separate independent root review; the coefficient and this composition
are being reviewed separately. The direct descent includes the explicit
repair of the primary source's second-coefficient degree estimate,
recorded in ISSUE_KS_SOURCE_DEGREE_v2.md. No frozen artifact or sealed
successful continuation result was changed.
