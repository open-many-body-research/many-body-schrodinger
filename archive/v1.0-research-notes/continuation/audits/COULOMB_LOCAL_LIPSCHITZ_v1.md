> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit local Lipschitz regularity through every Coulomb collision

Evidence category: **paper theorem** on the actual weak H2 domain.
The proof uses the explicit cusp factor, the independently derived
global boundedness estimate, and exactly \(3N\) elementary convolution
steps. It uses no unverified analytic germ, qualitative hypoellipticity
claim, or external Calderon–Zygmund regularity theorem.

## 1. Actual inputs and quantitative output

Let \(N\ge1\), \(Z\ge0\), \(E\in\mathbb R\), and let the actual spin
function \(\psi\in H^2(\mathbb R^{3N};\mathbb C^{2^N})\) solve
\(H_{N,Z}\psi=E\psi\), for the physical repulsive Coulomb Hamiltonian.
All norms use the spin square sum; derivatives use the full spatial
gradient or ordered Hessian. Set
\[
 d=3N,\quad J=N(N-1)/2,\quad U=\|\psi\|_2,\quad
 A_F=Z\sqrt N+J/\sqrt2,\quad G_\psi=2\sqrt{|E|+4NZ^2}.
\]
Let \(\mathfrak M=\mathfrak M_{N,Z,E}\) be the explicit constant in
COULOMB_GLOBAL_BOUNDEDNESS_v1.md. Fix \(R>0\). Define
\[
 \delta={R\over2(d+1)},\quad
 L={2\over\delta},\quad
 T_\eta={15\over\delta^2}+{4(d-1)\over R\delta},\quad
 \omega_d={2\pi^{d/2}\over\Gamma(d/2)},\quad
 V_*=\max\left(1,\left({\omega_dR^d\over d}\right)^{1/2}\right).
\]
Here \(\omega_d\) is the area of the unit sphere in \(\mathbb R^d\);
the ordinary gamma values at integer and half-integer arguments make
it an explicit geometric constant. Put
\[
 r_*={2d\over2d-1},\quad
 K_R={1\over\omega_d}
 \left({\omega_d(2R)^{\,d-(d-1)r_*}\over d-(d-1)r_*}\right)^{1/r_*},
\]
\[
 A=2A_F+2L,\qquad C=A_F^2+2|E|+T_\eta,\qquad
 Q=\max(1,K_R(A+CV_*)),
\]
\[
 m_0=e^{A_FR}\mathfrak M,\qquad
 g_0=e^{A_FR}(G_\psi+A_F),\qquad
 \mathcal L_R=e^{A_FR}
       \{(Q+1)^d(g_0+m_0)+A_Fm_0\}.                           \tag{L1}
\]
Then \(\psi\) has a unique continuous representative on \(B_{R/2}\)
and that representative satisfies
\[
 \boxed{\ |\psi(x)-\psi(y)|_{\rm spin}
       \le\mathcal L_R U\,|x-y|
             \quad(x,y\in B_{R/2}).\ }                        \tag{L2}
\]
The theorem applies at intersections of collision strata, including
the simultaneous collision. There is no eigenvalue isolation, binding,
positivity or rotation hypothesis in this regularity result.
It does not construct an eigenfunction.

## 2. Exact cusp factor and weak product rule

Define the real, explicitly physical function
\[
 F(x)=-Z\sum_i|x_i|+\tfrac12\sum_{i<j}|x_i-x_j|.                \tag{L3}
\]
It is globally Lipschitz, \(F(0)=0\), and
\[
 |\nabla F|\le A_F\quad\hbox{almost everywhere},\qquad
 |F(x)|\le A_F|x|,\qquad \Delta F=2V
                            \quad\hbox{in distributions}.    \tag{L4}
\]
For the gradient bound, the nuclear part has gradient norm at most
\(Z\sqrt N\). Each pair term has two opposite three-dimensional
gradient blocks, each of length \(1/2\), so its full norm is
\(1/\sqrt2\); summing \(J\) such terms proves the displayed bound.

In three dimensions, \(\Delta|y|=2/|y|\) distributionally.
Integrate by parts outside a ball of radius \(a>0\): the omitted
boundary term is \(O(a^2)\) for a fixed smooth test and vanishes as
\(a\downarrow0\). There is no delta distribution at the origin.
Slicing proves the nuclear formula in configuration space. For a
pair, \(\Delta_{x_i,x_j}|x_i-x_j|=4/|x_i-x_j|\), with the factor
two from the two gradients; equivalently use the normalized
orthogonal difference coordinate. This proves the last identity
in (L4), with exactly the physical coefficient \(1/2\) in (L3).

Every second derivative of a distance is bounded in absolute value
by a constant times its reciprocal distance away from its collision.
Those reciprocals are in L2 on every bounded configuration set,
since their singular variable has dimension three. The same cutoff
argument and slicing identify these as weak derivatives. Thus
\(F\in H^2_{\rm loc}\), with bounded first derivatives.

Global boundedness gives
\(\||\psi|_{\rm spin}\|_\infty\le\mathfrak M U\).
Consequently
\[
 \phi=e^{-F}\psi\in H^2_{\rm loc}.
\]
This product rule is licensed: on a bounded ball \(e^{-F}\) and its
gradient are bounded, its second derivatives are L2, and \(\psi\)
is bounded. The second-order product terms are all L2. One can
justify the identities by smoothing \(F\); its gradients stay
uniformly bounded, its second derivatives converge locally in L2,
and dominated convergence handles the terms with \(\nabla\psi\).
No multiplication of two uncontrolled Sobolev distributions occurs.

Substitute the product rule and \(\Delta F=2V\) in the actual
eigenfunction equation. The Coulomb term cancels exactly:
\[
 \Delta\phi=-2b\cdot\nabla\phi-c\phi,\qquad
 b=\nabla F,\qquad c=|b|^2+2E.                                \tag{L5}
\]
It is a weak equation with \(|b|\le A_F\) and
\(|c|\le A_F^2+2|E|\). The coefficients need not be analytic or
continuous at collisions. Only their boundedness is used below.

## 3. Initial norms without unknown physical derivatives

The full spin energy identity and the nuclear Hardy form bound give
\[
 \tfrac12\|\nabla\psi\|_2^2
 \le |E|U^2+2Z\sqrt N\,U\|\nabla\psi\|_2.
\]
Young's inequality leaves one quarter of the gradient square on
the left, hence
\(\|\nabla\psi\|_2\le G_\psi U\).
On \(B_R\), (L4) and the product rule therefore give
\[
 \||\phi|_{\rm spin}\|_\infty\le m_0U,\qquad
 \|\nabla\phi\|_{L^2(B_R)}\le g_0U.                            \tag{L6}
\]
These are the initial quantities in (L1). No physical C1 or
Lipschitz norm has been assumed.

## 4. A compactly supported Newton-kernel identity

In dimension \(d\ge3\), the distribution
\[
 \Gamma(x)=-{1\over(d-2)\omega_d}|x|^{2-d}
\]
satisfies \(\Delta\Gamma=\delta_0\); its coefficient and sign follow
by integrating the outward flux on a sphere. Its gradient has norm
\[
 |\nabla\Gamma(x)|={1\over\omega_d}|x|^{1-d}.
\]
For any compactly supported H2 function \(z\), distributional
convolution gives
\[
 z=\Gamma*\Delta z,\qquad \nabla z=(\nabla\Gamma)*\Delta z.      \tag{L7}
\]
Indeed derivatives can be moved between the factors when one is
compactly supported:
\(\Gamma*\Delta z=(\Delta\Gamma)*z=\delta_0*z=z\).
This identity does not require a harmonic correction or a boundary
condition at infinity. It can also be checked first for compact
smooth functions and passed to the weak domain.

If \(z\) is supported in \(B_R\) and only its gradient on \(B_R\)
is sought, the convolution uses distances \(|x-y|\le2R\).
The truncated gradient kernel has exactly the bound
\[
 \|\,|\nabla\Gamma|\mathbf1_{|x|<2R}\|_{L^{r_*}}=K_R<\infty,
 \qquad d-(d-1)r_*={d\over2d-1}>0.                            \tag{L8}
\]
Young's convolution inequality thus improves an Lq source to a
gradient in Lp whenever
\[
 {1\over p}={1\over q}-{1\over2d},\qquad q\le2d.                \tag{L9}
\]
For \(q=2d\), this is the L-infinity Holder convolution estimate.
For vector spin sources the pointwise Hilbert norm is bounded by
the same scalar convolution, so no spin or coordinate multiplicity
factor is lost.

## 5. Exactly d local gain steps with fixed reserves

For \(j=0,\ldots,d\), set
\[
 R_j=R-j\delta,\qquad {1\over q_j}={d-j\over2d}.
\]
Thus \(q_0=2\), \(q_{d-1}=2d\), \(q_d=\infty\), and
\(R_d=R(d+2)/(2(d+1))>R/2\).
Choose a radial C2 cutoff \(\eta_j\) equal to one on \(B_{R_{j+1}}\),
zero outside \(B_{R_j}\), using the fixed quintic step on the gap
\(\delta\). It has
\[
 |\nabla\eta_j|\le L,\qquad
 |\Delta\eta_j|\le T_\eta.                                   \tag{L10}
\]
Indeed its radial derivative is at most \(2/\delta\), its radial
second derivative at most \(15/\delta^2\), and its transition
radius is at least \(R/2\). The formula for \(T_\eta\) includes
the full \((d-1)/\rho\) radial term. The cutoff is constant near
zero and preserves the actual local H2 domain.

Let \(z_j=\eta_j\phi\), a compactly supported actual H2 function.
By (L5),
\[
 \Delta z_j=(-2\eta_j b+2\nabla\eta_j)\cdot\nabla\phi
                         +(\Delta\eta_j-\eta_jc)\phi.
\]
Assume \(\nabla\phi\in L^{q_j}(B_{R_j})\). The right side is
in that same Lq space, is supported in \(B_{R_j}\), and has norm
at most
\[
 A\|\nabla\phi\|_{L^{q_j}(B_{R_j})}
          +C\,V_*m_0U.                                      \tag{L11}
\]
This uses \(q_j\ge2\) and
\(|B_R|^{1/q_j}\le\max(1,|B_R|^{1/2})=V_*\).
Apply (L7)–(L9), and use \(\eta_j=1\) on the next ball. Writing
\(G_j=\|\nabla\phi\|_{L^{q_j}(B_{R_j})}\), this proves
\[
 G_{j+1}\le K_R(AG_j+CV_*m_0U)\le Q(G_j+m_0U).                \tag{L12}
\]
The induction is valid for the actual weak derivatives: (L7)
identifies the new convolution function with \(\nabla z_j\)
distributionally, and its improved integrability is supplied by
Young's inequality. No derivative has to exist classically before
it can be estimated. Every cutoff uses only two derivatives.

From (L6), (L12) and \(Q\ge1\),
\[
 G_d\le(Q+1)^d(g_0+m_0)U.                                    \tag{L13}
\]
For example the recursion follows from
\(G_{j+1}+m_0U\le(Q+1)(G_j+m_0U)\).
This is a finite sequence of exactly \(d=3N\) genuine
integrability gains. The last step starts with \(q=2d>d\)
and gives L-infinity; there is no unsupported critical Sobolev
endpoint assertion.

## 6. Actual Lipschitz representative and the local analytic input

The bounds (L6) and (L13) put \(\phi\) in
\(W^{1,\infty}(B_{R_d})\). A bounded weak gradient on a convex
ball gives a Lipschitz representative: mollify on slightly smaller
balls, apply the fundamental theorem of calculus on segments,
and pass to the limit with the common gradient bound.
This argument also works for the finite-dimensional spin target
with its Hilbert norm.

The function \(F\) is Lipschitz and bounded by \(A_FR\) there.
The actual product \(\psi=e^F\phi\) consequently has Lipschitz
constant at most
\[
 e^{A_FR}\{G_d+A_Fm_0U\}\le\mathcal L_RU
\]
on \(B_{R/2}\). It agrees almost everywhere with the original
H2 function, and continuous representatives agreeing almost
everywhere on a ball agree everywhere. This proves (L2).
In particular, it determines a canonical value at the simultaneous
collision, as needed by the local distance theorem.

For \(N=2\), taking \(R=2\) supplies explicit local Lipschitz data
on \(B_1\). Together with an actual scalar rotationally invariant
H2 eigenfunction, it supplies the previously explicit Lipschitz
premise in PHYSICAL_LOCAL_DISTANCE_ANALYTIC_v1.md.
The latter theorem then proves the physical G1 estimate with
weight one and all weights \(0<\sigma<1\).
The present theorem does not supply the eigenfunction or its
rotational symmetry; those remain physical spectral obligations.

## 7. Dependencies, primary scope and preservation

The elementary convolution proof above is given in full at the
needed exponents. No Calderon–Zygmund or external analytic
regularity theorem is used as an uninspected dependency.
This is a classical cusp-conjugation regularity mechanism, not
a novelty claim.

New paper dependencies:

| Artifact | SHA-256 |
|---|---|
| COULOMB_GLOBAL_BOUNDEDNESS_v1.md | d103aa471fcb626ca330d02a4cfbc6534a038e8827e129cff6c24ef3351377a7 |
| COULOMB_H2_TAIL_TRANSFER_v1.md | c518ebc59a4ad2d533bbc7d967bac1e1d536787f4312960294dd079640ceeaf6 |
| ../paper/CONFIGURATION_MULTIPLIER_FOURIER_BRIDGE_v1.md | ada2303f66a27f3870e5dfc18c4f99218d386e9a728d0aa8814bf3cb92eef26c |

The independent boundedness proof supplies the L-infinity input;
the reviewed Hardy/form proof supplies the actual energy and
multiplier bounds. This manuscript is not a kernel verification
of their composition.

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The precise downstream frozen target is the local Lipschitz input
in rwa_proof/RWA_THEOREM.md section 3, SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
No frozen or sealed successful artifact was modified. This new
proof is subject to independent review; no Lean claim is made.
