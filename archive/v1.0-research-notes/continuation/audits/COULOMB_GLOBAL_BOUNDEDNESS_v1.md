> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit global boundedness of actual Coulomb eigenfunctions

Evidence category: **paper theorem**. This is a direct truncated-power
iteration on the actual weak domain, with an elementary Sobolev proof
and explicit constants. It removes boundedness as an independent input
to the exterior analytic theorem when an actual H2 eigenfunction is
already available. It proves neither existence nor binding.

## 1. Exact statement

Let \(N\ge1\), \(Z\ge0\), and let \(\psi\) belong to the actual weak
space \(H^2(\mathbb R^{3N};\mathbb C^{2^N})\). Suppose
\[
 \left[-\tfrac12\Delta-Z\sum_i|x_i|^{-1}
            +\sum_{i<j}|x_i-x_j|^{-1}\right]\psi=E\psi,
 \qquad E\in\mathbb R,                                        \tag{M1}
\]
as an L2 equality. This allows the full fermionic spin space, without
assuming positivity, nondegeneracy or a chosen spatial symmetry sector.
Set
\[
 d=3N,\qquad \chi={d\over d-2},\qquad
 C_d={4d(d-1)^2\over(d-2)^2},\qquad
 B=1+|E|+4NZ^2,
\]
and
\[
 \mathfrak M_{N,Z,E}
   =(C_dB)^{d/4}\,2^{d/2}\,
                         \chi^{d(d-2)/4}.                     \tag{M2}
\]
Then the pointwise spin norm has essential bound
\[
 \boxed{\ 
 \left\|\left(\sum_\sigma|\psi_\sigma(\,\cdot\,)|^2\right)^{1/2}
                   \right\|_\infty
       \le\mathfrak M_{N,Z,E}\|\psi\|_2 .\ }                   \tag{M3}
\]
In particular, every scalar eigenfunction is bounded. There is no extra
factor depending on the number \(2^N\) of spin labels.

The constants are coarse and are not claimed to be optimal. The proof
uses the positive sign of the electron-pair potential: that term can
be dropped from the lower form bound. Reversing that physical sign
would require a different constant.

## 2. Elementary Sobolev inequality with a declared constant

We prove the sufficient bound
\[
 \|w\|_{L^{2d/(d-2)}}^2\le C_d\|\nabla w\|_2^2
                      \qquad(w\in H^1(\mathbb R^d),\ d\ge3).   \tag{M4}
\]
Here is an explicit product-integration proof of the required
W1,1 inequality. For nonnegative integrable functions \(F_i\) of all
coordinates except \(x_i\), repeated Holder gives
\[
 \int_{\mathbb R^d}\prod_{i=1}^d
           F_i(x_{\widehat i})^{1/(d-1)}\,dx
 \le\prod_{i=1}^d\left(\int_{\mathbb R^{d-1}}F_i\right)^{1/(d-1)}.
                                                                  \tag{M5}
\]
For completeness, prove (M5) by induction on \(d\). The case \(d=2\)
is Fubini. For \(d>2\), integrate \(x_d\) first and apply Holder
with \(d-1\) equal exponents to the factors \(i<d\). Write
\(G_i=\int F_i\,dx_d\). In the remaining \(d-1\) variables, apply
Holder to \(F_d^{1/(d-1)}\) and the product of the \(G_i\)'s,
with exponents \(d-1\) and \((d-1)/(d-2)\). The latter integral
is exactly the dimension-\((d-1)\) induction hypothesis, raised
to \((d-2)/(d-1)\). This gives (M5). Tonelli and truncation
justify the steps for nonnegative functions without preliminary
boundedness assumptions.

For \(u\in C_c^1(\mathbb R^d)\), the one-variable fundamental
theorem of calculus gives
\[
 |u(x)|\le F_i(x_{\widehat i})
       :=\int_{\mathbb R}|\partial_i u|\,dx_i.
\]
Multiply these \(d\) inequalities and apply (M5):
\[
 \|u\|_{d/(d-1)}
 \le\prod_i\|\partial_i u\|_1^{1/d}
 \le\sum_i\|\partial_i u\|_1.
\]
The last enlargement avoids optimizing the constant.
For smooth compactly supported \(w\), apply this to
\(u=|w|^\alpha\), where \(\alpha=2(d-1)/(d-2)>2\).
The chain rule and Cauchy-Schwarz yield
\[
 \|w\|_{2d/(d-2)}^\alpha
 \le\alpha\sqrt d\,
       \|w\|_{2d/(d-2)}^{\alpha-1}\|\nabla w\|_2.
\]
This uses \(2(\alpha-1)=2d/(d-2)\). If the norm is nonzero,
cancel it; if it is zero the assertion is immediate.
Squaring gives exactly \(C_d=\alpha^2d\).

Approximate an arbitrary H1 function by smooth compactly supported
functions in H1. The proved inequality makes the approximations
Cauchy in \(L^{2d/(d-2)}\), and their L2 convergence identifies the
new limit with the same function. This proves (M4) on the actual
weak domain. The approximation/density mechanism is the standard
cutoff and convolution construction also detailed in the continuum
bridge. No eigenfunction regularity is assumed in this extension.

## 3. Truncated weak tests, with complex phases retained

First take one scalar complex component \(v\) of \(\psi\). It satisfies
the same equation and is initially in H2, hence H1 and L2.
Suppose inductively that \(v\in L^p\) for some real \(p\ge2\).
For a finite \(L>0\), set
\[
 t_L=\min(|v|,L),\qquad
 \varphi_L=v\,t_L^{p-2},\qquad
 w_L=|v|\,t_L^{p/2-1}.                                        \tag{M6}
\]
Both nonlinear maps of \(v\) are globally Lipschitz for fixed
\(L,p\), vanish at zero, and hence give H1 functions.
The complex Sobolev chain rule follows by treating \(v\) as a
two-component real H1 map, approximating Lipschitz maps by smooth
maps and passing in the weak derivative identities. The elementary
inequality \(|\nabla|v||\le|\nabla v|\) holds almost everywhere.
Moreover
\[
 \overline{\varphi_L}v=w_L^2,\qquad
 \|w_L\|_2^2\le\|v\|_p^p.                                    \tag{M7}
\]

Take the real part of the weak eigenfunction equation tested with
\(\varphi_L\). This test is legitimate in H1: \(\Delta v\in L2\),
the actual Coulomb multiplier \(Vv\in L2\), and H1 approximation
extends the original compact-test identity to \(\varphi_L\).
The Coulomb form of \(w_L\) is also finite by configuration Hardy.

On \(|v|<L\), the radial derivative of (M6), together with the phase
part of \(\nabla v\), gives
\[
 \operatorname{Re}(\nabla v\cdot\nabla\overline{\varphi_L})
 \ge(p-1)|v|^{p-2}|\nabla|v||^2
 ={4(p-1)\over p^2}|\nabla w_L|^2.
\]
On \(|v|>L\), the corresponding lower bound is
\(|\nabla w_L|^2\), which is stronger because
\(4(p-1)/p^2\le1\). These identities hold almost everywhere,
including a harmless choice of weak derivative on the truncation
level set. Equivalently one can approximate the scalar minimum
by Lipschitz smooth truncations. The complex phase contributes a
nonnegative term and is not discarded with an incorrect equality.
It follows that
\[
 c_p\|\nabla w_L\|_2^2+\langle Vw_L,w_L\rangle
 \le E\|w_L\|_2^2,\qquad c_p={2(p-1)\over p^2}.                 \tag{M8}
\]

## 4. Nuclear Hardy absorption and one iteration step

Configuration Hardy gives
\[
 \langle Vw,w\rangle
 \ge-a\|w\|_2\|\nabla w\|_2,\qquad a=2Z\sqrt N,                \tag{M9}
\]
for every actual H1 function \(w\). The nonnegative pair potentials
were retained until this lower bound. This is exactly the argument
in the independently reviewed all-N tail-transfer proof.

Substitute (M9) into (M8), use \(|E|\), and absorb half of \(c_p\)
by Young's inequality:
\[
 \|\nabla w_L\|_2^2
 \le\left({2|E|\over c_p}+{a^2\over c_p^2}\right)\|w_L\|_2^2
 \le p^2(|E|+a^2)\|w_L\|_2^2
 \le p^2B\|w_L\|_2^2.                                        \tag{M10}
\]
The middle step uses \(p^2/(p-1)\le2p\le p^2\) and
\(p^4/[4(p-1)^2]\le p^2\), valid for every \(p\ge2\).
Applying (M4), then (M7), gives
\[
 \|w_L\|_{2\chi}^2\le C_dBp^2\|v\|_p^p.
\]
As \(L\) increases, the integrands \(|w_L|^{2\chi}\) increase
to \(|v|^{p\chi}\). Monotone convergence therefore proves the
actual next integrability statement and estimate
\[
 \|v\|_{p\chi}\le(C_dBp^2)^{1/p}\|v\|_p.                       \tag{M11}
\]
No untruncated high power was used as a test before its integrability
was proved, and no initial L-infinity bound was assumed.

## 5. Infinite product and spin summation

Starting with \(p_0=2\), set \(p_j=2\chi^j\).
Repeated use of (M11) gives
\[
 \|v\|_{p_{m+1}}
 \le\prod_{j=0}^m(C_dBp_j^2)^{1/p_j}\|v\|_2.
\]
The two sums determining the infinite product are exactly
\[
 \sum_{j\ge0}{1\over p_j}={d\over4},\qquad
 \sum_{j\ge0}{\log p_j\over p_j}
 ={d\over4}\log2+{d(d-2)\over8}\log\chi.                        \tag{M12}
\]
They follow from the geometric series and
\(\sum j q^j=q/(1-q)^2\), with \(q=(d-2)/d\).
Consequently every norm in the sequence is bounded by the right
side of (M3) for the scalar component.

This gives an essential supremum bound on the infinite-measure
configuration space without any finite-volume assumption. If a
positive-measure set had \(|v|>\mathfrak M\|v\|_2+\delta\),
its measure would be finite by \(v\in L2\), and the Lp norm on that
set would approach at least this larger value as \(p_j\to\infty\),
contradicting the uniform estimate.

Finally apply the scalar bound to each spin component. Outside the
union of the finitely many exceptional null sets,
\[
 \sum_\sigma|\psi_\sigma(x)|^2
 \le\mathfrak M_{N,Z,E}^2\sum_\sigma\|\psi_\sigma\|_2^2.
\]
Taking square roots proves (M3). The same statement holds on the
fermionic subspace; no scalar positivity assumption entered.

## 6. Physical analytic interface and precise limitations

For an actual scalar two-electron H2 eigenfunction satisfying the
rotational symmetry hypothesis, (M3) supplies the boundedness input
of EXTERIOR_DISTANCE_ANALYTIC_v1.md. Its resulting bound in X2 is
\(C_\infty\mathfrak M_{2,Z,E}\|\psi\|_2\), with the same explicit
inverse-linear radii. Rotational invariance, the existence of an
appropriate eigenfunction, and all spectral or algorithmic conclusions
remain separate.

This proof does not supply local Lipschitz regularity at the simultaneous
collision, nor the exponential L2 tail needed by the H2 tail transfer.
It does not claim efficient representation of the eigenfunction.
The Moser iteration mechanism is classical; no novelty is claimed
for the method or for boundedness of Coulomb eigenfunctions.

For historical context, the primary publisher page for J. Moser,
*A new proof of de Giorgi's theorem concerning the regularity problem
for elliptic differential equations* (1960), confirms the citation,
volume 13, pages 457–468:
https://doi.org/10.1002/cpa.3160130308.
The attempted publisher PDF redirected to its abstract/bibliography
page, so the full primary proof was inaccessible in this check.
It is not a logical dependency: (M4)–(M12) prove the particular
iteration needed here directly.

The new local Hardy/domain dependency is
../paper/CONFIGURATION_MULTIPLIER_FOURIER_BRIDGE_v1.md, SHA-256
ada2303f66a27f3870e5dfc18c4f99218d386e9a728d0aa8814bf3cb92eef26c.
The independently reviewed form argument is
COULOMB_H2_TAIL_TRANSFER_v1.md, SHA-256
c518ebc59a4ad2d533bbc7d967bac1e1d536787f4312960294dd079640ceeaf6.

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The downstream frozen target is the bounded physical exterior input in
rwa_proof/GLOBAL_DYADIC_ATTEMPT.md, SHA-256
b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
This new manuscript is subject to independent review. No frozen or
sealed successful artifact was modified; no Lean verification is claimed.
