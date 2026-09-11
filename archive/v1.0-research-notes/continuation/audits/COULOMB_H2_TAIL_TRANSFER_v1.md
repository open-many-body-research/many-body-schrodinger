> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exponential L2-to-H2 tail transfer for arbitrary electron count

Evidence category: **paper theorem**, with explicit constants.
This is a shared continuum estimate for the actual weak H2 domain and
the full finite spin space. It does not prove binding or the exponential
L2 tail supplied as input. In the two-electron approximation chain it
reduces G3 to that strictly weaker tail input and actual eigenfunction data.

## 1. Precise theorem and all constants

Let \(N\ge1\) be an integer, \(Z\ge0\), and
\[
 H_{N,Z}=-\tfrac12\Delta+V,\qquad
 V=-Z\sum_{i=1}^N|x_i|^{-1}
                      +\sum_{1\le i<j\le N}|x_i-x_j|^{-1}.
\]
Let \(\psi\) be in the actual weak Sobolev space
\(H^2(\mathbb R^{3N};\mathbb C^{2^N})\), and suppose
\(H_{N,Z}\psi=E\psi\) with \(E\in\mathbb R\), as an L2 equality.
One may additionally require simultaneous spatial-spin antisymmetry;
all estimates hold on the full spin space and restrict to that subspace.
No eigenvalue isolation or uniqueness is used.

Put
\[
 S(x)=\sum_i|x_i|,\qquad \rho(x)=\left(\sum_i|x_i|^2\right)^{1/2}.
\]
Suppose that, for some \(C_0\ge0\), \(\gamma>0\),
\[
 \|\psi\|_{L^2(S>R)}\le C_0e^{-\gamma R}\qquad(R\ge1).           \tag{T1}
\]
All norms include the spin square sum. The H2-star norm is
\[
 \|\psi\|_{H^2_*(A)}
 =\left(\|\psi\|_{L^2(A)}^2+\|\nabla\psi\|_{L^2(A)}^2
                              +\|D^2\psi\|_{F,L^2(A)}^2\right)^{1/2},
\]
where the Hessian includes all ordered pairs of the \(3N\) coordinates.

Define
\[
 \begin{split}
 J&=N(N-1)/2,\\
 K&=2Z\sqrt N+\sqrt{NJ},\\
 G&=2\sqrt{|E|+4NZ^2+2},\\
 B&=6|E|+6K^2+3/2,\\
 D&=6\{\,|E|+2G+(3N+14)/2\,\}+6K^2+3/2,\\
 C_t&=\max\{DC_0e^{2\gamma},
                          B\|\psi\|_2e^{3\gamma}\},\qquad
 \gamma_t=\gamma/\sqrt N.
 \end{split}                                                   \tag{T2}
\]
Then
\[
 \boxed{\ \|\psi\|_{H^2_*(S>R)}
             \le C_t e^{-\gamma_tR}\quad\hbox{for every }R\ge1.\ } \tag{T3}
\]
These constants deliberately sacrifice the L2 exponent by the displayed
factor \(1/\sqrt N\), using a smooth radial cutoff. The statement does
not identify this loss as optimal. No dependence on \(N\), spin dimension,
charge or energy is hidden in the proof.

## 2. Coulomb multiplier and form bounds

The ordinary three-dimensional Hardy inequality, extended to weak H1,
sliced in electron/spectator coordinates and summed in spin, gives
\[
 \|f/|x_i|\|_2\le2\|\nabla_i f\|_2,\qquad
 \|f/|x_i-x_j|\|_2\le\|\nabla_i f-\nabla_j f\|_2.               \tag{T4}
\]
The pair constant follows by the orthogonal coordinate
\((x_i-x_j)/\sqrt2\); the derivative and inverse-distance factors
cancel exactly. These are the configuration Hardy estimates in the
new continuum bridge, whose exact source is cited below.

Let \(g_i=\nabla_i f\), viewed as elements of the common Hilbert space
of three-vector L2 spin functions. Then
\[
 \sum_{i<j}\|g_i-g_j\|_2^2
    =N\sum_i\|g_i\|_2^2-\left\|\sum_i g_i\right\|_2^2
    \le N\|\nabla f\|_2^2.
\]
Cauchy-Schwarz over the \(J\) pairs and the triangle inequality for
the multiplication operator therefore give
\[
 \|Vf\|_2
 \le\left(2Z\sqrt N+\sqrt{NJ}\right)\|\nabla f\|_2
 =K\|\nabla f\|_2.                                            \tag{T5}
\]
For \(N=1\) the pair sum is empty and its contribution is zero.
The proof sums squared norms over spin before taking roots, so there
is no additional factor \(2^{N/2}\).

For the negative part of the quadratic form, the repulsive terms can
be discarded. Another Cauchy-Schwarz application to (T4) yields
\[
 \langle Vf,f\rangle
 \ge-2Z\sqrt N\,\|f\|_2\|\nabla f\|_2
 \ge-\tfrac14\|\nabla f\|_2^2-4NZ^2\|f\|_2^2.                  \tag{T6}
\]
All Coulomb integrals are finite for \(f\in H^1\): by (T4) each
inverse-distance multiplier belongs to L2, and its product with
\(\overline f\) is L1. Formula (T6) is valid for complex spin functions
with the usual real-valued Coulomb form.

## 3. A global graph estimate on the actual H2 domain

For \(f\in H^2\), the weak derivative Fourier identities and Plancherel give
\[
 \|D^2f\|_{F,2}=\|\Delta f\|_2,\qquad
 \|\nabla f\|_2^2\le\|f\|_2\|\Delta f\|_2.                       \tag{T7}
\]
The first identity includes the mixed Hessian entries:
\(\sum_{k,l}\xi_k^2\xi_l^2=(\sum_k\xi_k^2)^2\).
The second is Cauchy-Schwarz in Fourier space, including the spin sum.
It is not an estimate for only the diagonal second derivatives.

Young's inequality and (T5) give
\[
 \|Vf\|_2\le\tfrac14\|\Delta f\|_2+K^2\|f\|_2.
\]
Since \(-\Delta f/2=Hf-Vf\), rearrangement yields
\[
 \|\Delta f\|_2\le4\|Hf\|_2+4K^2\|f\|_2.
\]
Using \(\|\nabla f\|_2\le(\|f\|_2+\|\Delta f\|_2)/2\),
\[
 \|f\|_{H^2_*}
 \le\|f\|_2+\|\nabla f\|_2+\|D^2f\|_{F,2}
 \le6\|Hf\|_2+(6K^2+3/2)\|f\|_2.                              \tag{T8}
\]
In particular, \(\|\psi\|_{H^2_*}\le B\|\psi\|_2\).
This estimate neither presumes a spectral gap nor invokes a spectral
characterization of the graph norm.

## 4. Exterior Caccioppoli bound with only L2 data

Use the C2 step
\[
 \Theta(t)=0\ (t\le0),\qquad
 \Theta(t)=10t^3-15t^4+6t^5\ (0<t<1),\qquad
 \Theta(t)=1\ (t\ge1).
\]
It obeys \(0\le\Theta\le1\), \(|\Theta'|\le2\),
\(|\Theta''|\le15\), including the joined endpoints.
Fix \(t\ge3\), and set
\[
 \chi(x)=\Theta(\rho(x)-(t-2)),\qquad
 \eta(x)=\Theta(\rho(x)-(t-1)).                                 \tag{T9}
\]
Both are constant near the nonsmooth point of \(\rho\) at zero and
belong to \(W^{2,\infty}\). They preserve the actual weak H2 domain
under multiplication. Their derivatives are supported in the
respective radial annuli, and
\[
 |\nabla\chi|,|\nabla\eta|\le2,\qquad
 |\Delta\eta|\le15+{2(3N-1)\over t-1}\le3N+14.                  \tag{T10}
\]
The last inequality uses \(t-1\ge2\). The radial Laplacian formula
is used only on this positive-radius annulus.

Taking the real part of the equation paired with \(\chi^2\psi\)
and expanding the gradient gives the exact localization identity
\[
 \tfrac12\|\nabla(\chi\psi)\|_2^2
       +\langle V\chi\psi,\chi\psi\rangle
 =E\|\chi\psi\|_2^2+\tfrac12\|(\nabla\chi)\psi\|_2^2.            \tag{T11}
\]
The identity is licensed by \(\psi\in H^2\), bounded weak derivatives
of \(\chi\), the H1 multiplier bound and integration by parts in the
actual weak domain. Compact support is unnecessary: alternatively
one may first apply an outer spatial cutoff and pass to the limit
in these finite L2 and L1 terms.

Applying (T6) and (T10) gives
\[
 \|\nabla(\chi\psi)\|_2
 \le G\|\psi\|_{L^2(\rho>t-2)}.                               \tag{T12}
\]
Indeed one quarter of the gradient-square remains on the left of
(T11), and the right side is at most
\((|E|+4NZ^2+2)\|\psi\|_{L^2(\rho>t-2)}^2\).
Only the outer L2 mass appears. This is not an invocation of an
already established derivative tail.

## 5. Cutoff commutator and decay transfer

The actual H2 product rule gives
\[
 H(\eta\psi)=E\eta\psi-\nabla\eta\cdot\nabla\psi
                                  -\tfrac12(\Delta\eta)\psi.   \tag{T13}
\]
On the support of \(\nabla\eta\), \(\chi=1\) and
\(\nabla(\chi\psi)=\nabla\psi\) almost everywhere. Thus (T10)–(T12)
imply
\[
 \|H(\eta\psi)\|_2
 \le\{\,|E|+2G+(3N+14)/2\,\}
                          \|\psi\|_{L^2(\rho>t-2)}.
\]
The function \(\eta\psi\) is in the actual H2 domain, so (T8) applies.
Since \(\eta=1\) on \(\rho>t\), its weak derivatives there are
the actual derivatives of \(\psi\). Consequently
\[
 \|\psi\|_{H^2_*(\rho>t)}
 \le D\,\|\psi\|_{L^2(\rho>t-2)}.                              \tag{T14}
\]
The radial cutoff depends symmetrically on all electron coordinates
and acts trivially in spin, so this argument also stays inside the
fermionic space when the initial function is fermionic.

The exact norm comparisons are
\[
 \rho\le S\le\sqrt N\,\rho.
\]
For \(R\ge3\sqrt N\), take \(t=R/\sqrt N\ge3\). Then
\(\{S>R\}\subset\{\rho>t\}\) and
\(\{\rho>t-2\}\subset\{S>t-2\}\). Since \(t-2\ge1\), (T1) and
(T14) give
\[
 \|\psi\|_{H^2_*(S>R)}
 \le DC_0e^{-\gamma(t-2)}
 =DC_0e^{2\gamma}e^{-\gamma R/\sqrt N}.                         \tag{T15}
\]
For \(1\le R\le3\sqrt N\), the global graph bound gives
\[
 \|\psi\|_{H^2_*(S>R)}
 \le B\|\psi\|_2
 \le B\|\psi\|_2e^{3\gamma}e^{-\gamma R/\sqrt N}.
\]
The two ranges prove (T3) with exactly the constants in (T2).

## 6. Exact scope, dependencies and preservation

The new conclusion is a uniform physical derivative-tail bound on the
full configuration and spin space for every finite positive \(N\).
For \(N=2\) it supplies precisely the norm and exponential form of G3
from an actual H2 eigenfunction with an exponential L2 tail.
It does not establish that such a tail exists when an atom fails to
bind all electrons. No assertion about arbitrary-N binding is made.
It also does not turn energy accuracy into wavefunction accuracy.

The configuration Hardy and weak Fourier facts used in (T4) and (T7)
are detailed in the newly inspected paper
../paper/CONFIGURATION_MULTIPLIER_FOURIER_BRIDGE_v1.md, SHA-256
ada2303f66a27f3870e5dfc18c4f99218d386e9a728d0aa8814bf3cb92eef26c.
They are used here as paper mathematical facts; this manuscript does
not infer a kernel proof from the presence of separate compiled
component modules.

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The frozen tail target is rwa_proof/GLOBAL_DYADIC_ATTEMPT.md,
SHA-256 b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
The exact new G3 target is ENDPOINT_ONE_THIRD_v3.md, SHA-256
cd7cf2878fe44a81dfd9c5247b2d613127a97341efefbe91ebd3221eb4369b1a.

The finite checker verifies the pair-gradient identity and the displayed
algebraic constants on exact rational instances. The all-function
Sobolev and PDE arguments are the paper proof above. A separate
independent review is still required for this new manuscript.
No frozen or sealed successful artifact was modified.
