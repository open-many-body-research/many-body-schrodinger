> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Codimension-four L2 removability and the actual weak KS equation

Evidence category: **paper proof**. This is a local distributional operator
lemma and an explicit application to actual KS pullbacks. It is not a Lean
proof, a construction of a physical eigenfunction or a spectral identification.
No distributional chain rule through the rank-deficient map at \(y=0\) is
assumed.

## 1. Exact removability statement

Let
\[
 \Omega=(-a,a)^4\times(t_0+(-b,b)^3),\qquad a,b,c>0,\qquad
 \Sigma=\{(y,t)\in\Omega:y=0\},
\]
\[
 P_c=-\Delta_y-c|y|^2\Delta_t,\qquad Q=P_c+B,\qquad
 B\in L^\infty_{\rm loc}(\Omega).
\]
Suppose \(u,f\in L^2_{\rm loc}(\Omega)\) and
\[
 Qu=f\quad\hbox{in }\mathcal D'(\Omega\setminus\Sigma).              \tag{K1}
\]
Then the identical equation holds in \(\mathcal D'(\Omega)\). Complex
coefficients and functions are permitted; no smallness, positivity or
analyticity of \(B\) is required.

Pairings below are bilinear: the desired weak statement is
\[
 \int_\Omega u(P_c\phi+B\phi)=\int_\Omega f\phi,
                  \qquad \phi\in C_c^\infty(\Omega).                \tag{K2}
\]
Thus no conjugation of the potential is implicit. Since \(|y|^2\) is
independent of \(t\), \(P_c\) equals its distributional transpose.

## 2. Exact hole cutoff and defect bound

Fix a test \(\phi\), and choose \(a'<a,b'<b\) so that
\[
 K_0=[-a',a']^4\times T,\qquad T=t_0+[-b',b']^3
\]
contains its support in its relative interior. Put
\[
 V_T=(2b')^3,\quad 0<\delta_0\le\min(1,a'/4),\quad
 M_B=\mathop{\rm ess\,sup}_{K_0}|B|.
\]
Use the C2 step function
\[
 \Theta(s)=
 \begin{cases}0&s\le0,\\10s^3-15s^4+6s^5&0\le s\le1,\\1&s\ge1.
 \end{cases}
\]
It satisfies \(0\le\Theta\le1\), \(|\Theta'|\le2\), \(|\Theta''|\le15\).
For \(0<\delta\le\delta_0\), define
\[
 \chi_\delta(y)=\Theta((|y|-\delta)/\delta).
\]
It vanishes for \(|y|\le\delta\), equals one for \(|y|\ge2\delta\), and
its derivatives are supported in \(A_\delta=\{\delta<|y|<2\delta\}\).
The four-dimensional radial formula gives
\[
 |\nabla_y\chi_\delta|\le2\delta^{-1},\qquad
 |\Delta_y\chi_\delta|
 \le\delta^{-2}|\Theta''|+{3\over|y|\delta}|\Theta'|
 \le21\delta^{-2}.                                                \tag{K3}
\]
The exact transverse volumes are
\[
 |A_\delta|={15\pi^2\over2}\delta^4,\qquad
 |B_4(0,2\delta)|=8\pi^2\delta^4.                                  \tag{K4}
\]
Set
\[
\begin{split}
 U_\delta&=\|u\|_{L^2(B_4(0,2\delta)\times T)},&
 F_\delta&=\|f\|_{L^2(B_4(0,2\delta)\times T)},\\
 \Phi_0&=\|\phi\|_\infty,&
 \Phi_1&=\|\nabla_y\phi\|_\infty,\\
 \Phi_Q&=\|\Delta_y\phi\|_\infty+
      4c\delta_0^2\|\Delta_t\phi\|_\infty+M_B\Phi_0,\\
 C_A&=\pi\sqrt{15/2},& C_V&=2\sqrt2\pi.
\end{split}                                                       \tag{K5}
\]
The tube lies in \(K_0\). The desired defect has the explicit bound
\[
\begin{split}
 |\langle Qu-f,\phi\rangle|
 \le\sqrt{V_T}\bigl[
 U_\delta\{C_A(21\Phi_0+4\delta\Phi_1)+C_V\delta^2\Phi_Q\}
             +C_V\delta^2F_\delta\Phi_0\bigr].                    \tag{K6}
\end{split}
\]

Here is the proof, including all commutator terms. Apply (K1) to
\(\chi_\delta\phi\). This test is C2 rather than smooth, but its compact
support stays a positive distance from both \(\Sigma\) and the outer
boundary. Approximation by smooth tests there in H2 is valid: the coefficients
of \(P_c\) and \(B\) are bounded on the containing compact set, and all
pairings converge by Cauchy--Schwarz against \(u,f\in L^2\).

The complete product identity is
\[
 Q(\chi_\delta\phi)=\chi_\delta Q\phi
    -2\nabla_y\chi_\delta\cdot\nabla_y\phi
    -(\Delta_y\chi_\delta)\phi.                                   \tag{K7}
\]
There are no \(t\)-cutoff terms because \(\chi_\delta\) depends only on \(y\);
the potential commutes with the cutoff. The first-order cross term is retained.
Subtract the zero pairing of (K1) with this test from the desired pairing.
The part involving \(1-\chi_\delta\) is bounded by
\[
 C_V\delta^2\sqrt{V_T}(U_\delta\Phi_Q+F_\delta\Phi_0),                \tag{K8}
\]
using \(|Q\phi|\le\Phi_Q\) on the tube. The two terms of (K7) are bounded by
\[
 C_A\sqrt{V_T}\,U_\delta(4\delta\Phi_1+21\Phi_0),                   \tag{K9}
\]
using the annulus volume (K4). This proves (K6).

The tubes shrink to \(\{0\}\times T\), a Lebesgue-null subset of \(\mathbb R^7\).
Absolute continuity of the integrals of \(|u|^2\) and \(|f|^2\) therefore gives
\(U_\delta,F_\delta\to0\). All remaining factors of (K6) are fixed or bounded.
Taking \(\delta\downarrow0\) proves (K2).

No estimate on \(\nabla_yu\), no trace of \(u\) on \(\Sigma\), and no
integration by parts differentiating \(u\) was used. This is why the argument
applies at the actual weak-input stage.

## 3. Uniform families and the exact integrability threshold

For a parameter family, (K6) has common constants when \(c\), the chart and
the local bounds on \(B\) are common. Uniform global L2 bounds alone need
not give a uniform rate of decay of the tube masses; each individual limit
suffices for the theorem.

If instead \(|u_\varepsilon|\le U_\infty\) and
\(|f_\varepsilon|\le F_\infty\) uniformly on \(K_0\), then
\[
 U_\delta\le C_V\delta^2\sqrt{V_T}U_\infty,\qquad
 F_\delta\le C_V\delta^2\sqrt{V_T}F_\infty.
\]
Consequently the uniform defect estimate is
\[
\begin{split}
 |\langle Qu-f,\phi\rangle|\le V_T\bigl[
 C_AC_VU_\infty\delta^2(21\Phi_0+4\delta\Phi_1)
 +C_V^2\delta^4(U_\infty\Phi_Q+F_\infty\Phi_0)\bigr].              \tag{K10}
\end{split}
\]
Thus the common physical L-infinity amplitude gives an explicit
\(O(\delta^2)\) rate.

Four transverse dimensions are critical for this L2 proof: the cutoff
Laplacian norm scales as \(\delta^{4/2-2}=1\), and the vanishing L2 mass
supplies the limit. In three transverse dimensions,
\[
 u(y,t)=|y|^{-1},\quad B=f=0
\]
is locally L2 and solves the same equation off \(y=0\), but
\[
 P_cu=4\pi\,\delta_{y=0}\otimes1_t.
\]
This follows by the flux of \(-\nabla|y|^{-1}\) through a small sphere.
In four dimensions the analogous function \(|y|^{-2}\) has flux \(4\pi^2\),
but it fails local L2 since
\[
 \int_0^r s^3|s^{-2}|^2\,ds=\infty.
\]
It belongs locally to every \(L^p\), \(p<2\), and retains its nonzero
distributional defect. Thus a blanket replacement of L2 by such \(L^p\)
integrability would be false.

## 4. Explicit KS computation away from the degeneracy

Use the KS convention
\[
 K(y)=\bigl(2(y_1y_3+y_2y_4),\
           2(y_2y_3-y_1y_4),\
           y_1^2+y_2^2-y_3^2-y_4^2\bigr).                        \tag{K11}
\]
Its exact polynomial identities are
\[
 |K(y)|^2=|y|^4,\qquad \Delta_yK_j=0,\qquad
 DK(y)DK(y)^T=4|y|^2I_3.                                       \tag{K12}
\]
The ordinary chain rule for a C2 function at the image point gives
\[
 \Delta_y\bigl(\Psi(K(y),t)\bigr)
        =4|y|^2(\Delta_X\Psi)(K(y),t).                           \tag{K13}
\]
Only points \(y\ne0\) are used at this stage. Orthogonally equivalent KS
conventions satisfying (K12) give the identical operator normalization.

Let \(a_X,a_t>0\), and let the actual function \(\Psi\) satisfy, classically
away from \(X=0\),
\[
 \left[-a_X\Delta_X-a_t\Delta_t+\lambda/|X|+W(X,t)\right]\Psi=0,    \tag{K14}
\]
where \(W\) is locally bounded at the isolated collision chart and smooth
away from the excluded physical collisions. Put \(u(y,t)=\Psi(K(y),t)\).
Multiplication by \(4|y|^2/a_X\) gives, for \(y\ne0\),
\[
 \left[-\Delta_y-{4a_t\over a_X}|y|^2\Delta_t+B(y,t)\right]u=0,
\qquad
 B(y,t)={4\lambda\over a_X}
             +{4\over a_X}|y|^2W(K(y),t).                        \tag{K15}
\]
The singular term has canceled, leaving a locally bounded \(B\).
If the actual pullback \(u\) is locally L2, Sections 1–2 extend (K15)
to the full lifted chart. Locally bounded \(\Psi\) suffices, since the
image of a compact lifted chart is compact.

## 5. Applicability to the physical distributional solution

Suppose \(\psi\) is an actual locally Lipschitz distributional solution
of the specified two-electron Coulomb eigenvalue equation. Work on an
isolated-pair chart where every other Coulomb denominator is bounded away
from zero.

Away from all collisions, the physical operator has smooth coefficients
and constant positive kinetic coefficients. C2 regularity there is not an
extra analytic hypothesis: locally the equation is
\[
 -\sum_i a_i\partial_i^2\psi=g\psi,\qquad a_i>0,\quad g\in C^\infty.
\]
Starting from local L2, the ordinary weak elliptic estimate, obtained by
local convolution, an energy estimate and the compact-support identity
\(\|D^2w\|_2=\|\Delta w\|_2\) after a fixed linear coordinate change,
gives H2 on a smaller box. The Leibniz rule and repeated finite applications
give all finite Sobolev orders on smaller boxes. The elementary
product-interval embedding used in the sealed factorial lemma then gives
C-infinity regularity. This finite argument merely licenses the classical
calculation off the collision; it supplies no claimed uniform analytic
constants.

Thus the physical scaled function in (K14) is C2 at each noncollision image,
and its actual KS pullback is locally bounded. It satisfies (K15) classically
away from \(y=0\) and distributionally everywhere by removability. The local
Lipschitz property is still an explicit physical input; this result does
not construct that physical solution.

For the nuclear chart set
\[
 \Psi_\varepsilon(X,t)=\psi(\varepsilon X,\varepsilon t),\qquad
 a_X=a_t=1/2,\quad\lambda=-\varepsilon Z,
\]
\[
 W_\varepsilon(X,t)=
 \varepsilon\left(-{Z\over|t|}+{1\over|X-t|}\right)-\varepsilon^2E.
\]
Then the exact full weak lifted operator is
\[
 Q_\varepsilon=-\Delta_y-4|y|^2\Delta_t+B_\varepsilon,
\]
\[
 B_\varepsilon=-8\varepsilon Z+
 8\varepsilon|y|^2\left(-{Z\over|t|}+{1\over|K(y)-t|}\right)
 -8\varepsilon^2E|y|^2.                                        \tag{K16}
\]

For the electron--electron chart set
\[
 \Psi_\varepsilon(X,t)=
 \psi\bigl(\varepsilon(t+X/2),\varepsilon(t-X/2)\bigr).
\]
Its kinetic operator before scaling is \(-\Delta_X-\tfrac14\Delta_t\).
Thus \(a_X=1,a_t=1/4,\lambda=\varepsilon\), and
\[
 W_\varepsilon(X,t)=
 -\varepsilon Z\left({1\over|t+X/2|}+{1\over|t-X/2|}\right)
 -\varepsilon^2E.
\]
The exact full weak lifted operator is
\[
 Q_\varepsilon=-\Delta_y-|y|^2\Delta_t+B_\varepsilon,
\]
\[
 B_\varepsilon=4\varepsilon-
 4\varepsilon Z|y|^2
 \left({1\over|t+K(y)/2|}+{1\over|t-K(y)/2|}\right)
 -4\varepsilon^2E|y|^2.                                        \tag{K17}
\]
These are precisely the frozen normalizations \(c=4\) and \(c=1\),
with the original kinetic energy and repulsive electron--electron term.

## 6. The actual scaled difference and composition

Fix \(0<\varepsilon\le\varepsilon_0\) and a common lifted chart such that
the images of that chart under every physical scaling in this interval
stay inside one neighborhood on which the following Lipschitz bound holds.
The isolated spectator separations and the outer coefficient neighborhoods
are retained throughout this same scale interval.

Let \(a_0=\psi(0,0)\), and suppose \(L_\psi\) is a common Lipschitz
constant in the physical neighborhood. On a fixed lifted box put
\(R_y=\sup|y|\), \(R_t=\sup|t|\). The physical displacement divided by
\(\varepsilon\) is at most
\[
 D_X=\sqrt{R_y^4+R_t^2}\quad\hbox{in the nuclear chart},\qquad
 D_X=\sqrt{2R_t^2+R_y^4/2}\quad\hbox{in the pair chart}.
\]
Therefore the actual difference
\[
 v_\varepsilon=(u_\varepsilon-a_0)/\varepsilon
\]
has the common bound
\[
 \|v_\varepsilon\|_\infty\le L_\psi D_X.                           \tag{K18}
\]
Since \(Q_\varepsilon a_0=B_\varepsilon a_0\), the full weak lifted equation
just proved implies
\[
 Q_\varepsilon v_\varepsilon
             =-a_0B_\varepsilon/\varepsilon                      \tag{K19}
\]
on the whole chart. This concerns the actual pullback, with no source
supported on \(y=0\). If \(B_\varepsilon/\varepsilon\) has the common
analytic derivative bounds on an outer box, then:

1. The actual locally Lipschitz physical distributional solution and
   spectator separation give (K19).
2. The amplitude (K18) and finite coefficient/source bounds give uniform
   H12 on a fixed inner box by the sealed weak initialization lemma.
3. All-order coefficient/source bounds and that H12 norm give the uniform
   factorial estimate by the sealed direct recurrence.

This removes the weak-lift gap in that conditional paper chain. The physical
solution and regularity inputs, quantitative KS descent to distances,
coordinate-boundary compatibility and continuum spectral identification
remain separate. This document alone does not discharge physical G1 or
full Theorem T.

## 7. Provenance, preservation and review boundary

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen annotated tag: theorem-t-proof-freeze-2026-09-09.
Frozen relative paths below are relative to THEOREM_T_FREEZE_2026-09-09_212604/.

| Frozen source | SHA-256 | Exact use |
|---|---|---|
| rwa_proof/KS_SOURCE_AUDIT.md | 0cada7c07aeb7a0680ad4b2e26977beff8c1de3250086c8196eb25d3a94db08f | Weak-lift premise and physical normalizations |
| rwa_proof/UNIFORM_ANALYTIC_AUDIT.md | 5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c | Scaled operators and physical amplitude |
| rwa_proof/RWA_THEOREM.md | d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09 | Distributional premise before the uniform lift |

New sealed dependencies in this directory:

* GRUSHIN_H12_WEAK_INITIALIZATION_v1.md, SHA-256
  ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812.
* GRUSHIN_FACTORIAL_RECURRENCE_v1.md, SHA-256
  5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594.

Sections 1–4 are proved directly here, without an external hypoellipticity
theorem. The auxiliary ks_removability_checks_v1.py checks the exact
polynomial identities and cutoff constants; it does not prove the
distributional limiting argument.

No inherited mathematical claim was refuted, and no frozen or previously
sealed artifact was changed. Independent review and final immutable hashes
are recorded separately before sealing this version.
