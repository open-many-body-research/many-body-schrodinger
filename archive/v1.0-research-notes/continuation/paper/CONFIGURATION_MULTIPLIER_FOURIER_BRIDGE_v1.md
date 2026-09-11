> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Configuration Hardy bounds and the actual weak-H²/Fourier bridge, v1

**Evidence:** detailed paper proof and exact interface audit. This is a new
supplement to CONTINUUM_FOUNDATIONS_v2.md, not a claim that F02–F04 have been
fully formalized. Separately compiled lemmas have their own source/build
receipts. The paper below does not itself constitute a kernel proof.

**Preservation:** no original artifact was modified. Historical reference:
frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, annotated tag
theorem-t-proof-freeze-2026-09-09. The actual definitions used here are in
AUDIT_2026-09-09_v1/lean/ContinuumFoundation_v1.lean, SHA-256
4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e.

## 1. Exact configuration and spin spaces

The existing definitions are Coordinate N = Fin N × Fin 3,
Configuration N = EuclideanSpace ℝ (Coordinate N), and Position =
EuclideanSpace ℝ (Fin 3). Lebesgue measure is determined by this Euclidean
structure. Write \(x_i\in\mathbb R^3\) for the electron-\(i\) coordinates.
SpinConfiguration N = Fin N → Fin 2, and SpinSpace N is PiLp 2 of the actual
scalar L² spaces, indexed by SpinConfiguration N. Consequently,

\[
 \|\psi\|^2=\sum_\sigma\int|\psi_\sigma|^2,\qquad
 G_i^2=\sum_{\sigma,\alpha}\|D_{i,\alpha}\psi_\sigma\|_2^2,
 \qquad G^2=\sum_iG_i^2.                                      \tag{1}
\]

There is no factor \(2^N\) or \(2^{N/2}\) in the estimates below. This is the
defining norm identity, available as PiLp.norm_sq_eq_of_L2. Sum squared
component estimates before taking a square root. All estimates hold on the
full spin space and hence on its simultaneous space-and-spin antisymmetric
subspace without imposing a separate spatial symmetry sector.

For N = 0, configuration space is zero-dimensional with Lebesgue mass one;
the derivatives and Coulomb sums are empty, so all multiplier assertions
reduce to zero. Statements using an electron index presuppose it exists.

## 2. Electron/spectator decomposition and compact nuclear Hardy

Fix \(i\in\operatorname{Fin}N\), and define
\[
 I_i=\{(j,\alpha):j\ne i\},\qquad
 S_i=\operatorname{EuclideanSpace}(\mathbb R,I_i).
\]
The coordinate bijection sends \((i,\alpha)\) to \(\alpha\) in the left
summand of Fin 3 ⊕ I_i and all other coordinates to the right summand.
It induces the linear isometry
\[
 C_i:\operatorname{Configuration}N
       \longrightarrow \operatorname{WithLp}_2(\mathbb R^3\times S_i),
       \qquad C_i x=(x_i,s_i(x)).                              \tag{2}
\]
Write \(A_i(y,s)\) for its inverse: electron \(i\) has position \(y\), with
all other coordinates given by \(s\).

The ordinary Cartesian product is used for product measure; its default
norm is not the L² product norm. The exact formal chain is
configurationSplit, followed by WithLp.volume_preserving_ofLp; the inverse
chain uses WithLp.volume_preserving_toLp. Hence, for every nonnegative
measurable function, including one whose integral is infinite,
\[
 \int F(x)\,dx=\int_{S_i}\int_{\mathbb R^3}F(A_i(y,s))\,dy\,ds.   \tag{3}
\]
For N = 1, the spectator space has dimension zero and measure one. There is
no Jacobian factor and no exceptional spectator set to discard. The actual
definitions and Tonelli identity are in lean/ConfigurationSlicing_v2.lean;
the inspected source SHA-256 is
087b0da32038b810915b73f0cc594409414accc6f3304080712c50fe110c7a77.

Let \(u\in C_c^1(\mathbb R^{3N};\mathbb C)\). For each fixed spectator \(s\),
\[
 u_s(y)=u(A_i(y,s)),\qquad
 \partial_\alpha u_s(y)=D_{i,\alpha}u(A_i(y,s)).                \tag{4}
\]
Each slice is C¹ and compactly supported. Indeed, the support is closed, and
boundedness of the ambient support bounds \(y\); equivalently the slice map
is a proper affine embedding. This uses classical slices, not weak slicing.

Apply the compact complex three-dimensional Hardy inequality to \(u_s\):
\[
 \int_{\mathbb R^3}\frac{|u_s(y)|^2}{|y|^2}\,dy
       \le4\int_{\mathbb R^3}\sum_\alpha|\partial_\alpha u_s|^2\,dy.
\]
Integrating in \(s\) using nonnegative Tonelli gives
\[
 u/|x_i|\in L^2,\qquad
 \int\frac{|u|^2}{|x_i|^2}\le4\sum_\alpha\|D_{i,\alpha}u\|_2^2. \tag{5}
\]
Finiteness of the right side follows from ambient compact C¹ regularity, so
it need not be assumed to invoke Tonelli. Measurability of the product and
memLp_two_iff_integrable_sq_norm give the requested MemLp statement.

The compact R³ theorem is
TheoremT.Hardy.complex_hardy_memLp_two_and_bound in
lean/HardyLimitComplexL2_v1.lean, inspected SHA-256
a842f223871d8f4614cc088a8c3e5d783852aa8df96fc190dc40a2656141f352.
Its actual hypotheses are ContDiff ℝ 1 and HasCompactSupport, and its
conclusion includes both MemLp of division by the norm and the constant-4
squared integral bound. At a pole, Lean's totalized inverse is zero.
Collision nullity identifies this representative with the physical singular
potential; it is not needed just to show this representative is measurable.

## 3. Pair coordinates: a short route and a sharper route

**Translation route.** For \(i\ne j\), \(x_j(A_i(y,s))=a(s)\) is independent
of \(y\). Apply R³ Hardy to \(y\mapsto u(A_i(y+a(s),s))\).
Translation preserves volume, and differentiation still gives the
electron-\(i\) derivative. Integrate in spectators:
\[
 \|u/|x_i-x_j|\|_2\le2\|\nabla_i u\|_2.
\]
The same argument with \(j\) gives, after the spin square sum,
\[
 \|\psi/|x_i-x_j|\|\le2\min(G_i,G_j)\le G_i+G_j.                \tag{6}
\]
Thus Coulomb membership and the specification's constant do not need to wait
for a global pair rotation in Lean.

**Orthogonal route.** Define \(R_{ij}\) on the actual configuration space by
\[
 z_i=(x_i-x_j)/\sqrt2,\quad z_j=(x_i+x_j)/\sqrt2,\quad
 z_k=x_k\ (k\ne i,j).
\]
Each of the three two-dimensional blocks is
\[
 2^{-1/2}\begin{pmatrix}1&-1\\1&1\end{pmatrix};
\]
it is orthogonal with determinant 1. The whole map is orthogonal with
determinant 1; its inverse has
\[
 x_i=(z_i+z_j)/\sqrt2,\qquad x_j=(-z_i+z_j)/\sqrt2.
\]
Volume preservation can be formalized directly from its linear isometry.
For \(v=u\circ R_{ij}^{-1}\),
\[
 D_{z_{i,\alpha}}v
    =2^{-1/2}(D_{i,\alpha}u-D_{j,\alpha}u)\circ R_{ij}^{-1},
 \qquad |z_i|=|x_i-x_j|/\sqrt2 .
\]
Applying (5) to \(v\), the left side becomes
\(2\|u/|x_i-x_j|\|_2^2\), and the right side becomes
\(2\sum_\alpha\|D_{i,\alpha}u-D_{j,\alpha}u\|_2^2\). Cancelling 2,
\[
 \boxed{\ \|u/|x_i-x_j|\|_2^2
     \le\sum_\alpha\|D_{i,\alpha}u-D_{j,\alpha}u\|_2^2.\ }      \tag{7}
\]
Using the unnormalized difference as an orthogonal coordinate would miss a
derivative or Jacobian factor. Both factors have been accounted for here.

## 4. Extension to the actual weak domain without assuming weak slices

WeakPartial f g k is the existing identity
\[
 \int\phi g=-\int(D_k\phi)f                                  \tag{8}
\]
for every real smooth compactly supported test. HasH1 supplies L² witnesses
\(g_k\); HasH2 additionally supplies L² witnesses \(e_{kl}=D_lg_k\) for every
ordered pair. These definitions concern actual weak derivatives.

Here is the precise density proof needed to extend (5)–(7). Choose real
\(\chi\in C_c^\infty\), \(0\le\chi\le1\), equal to 1 on the unit ball, and
put \(\chi_R(x)=\chi(x/R)\), \(R\ge1\). For \(f\in H^1\),
\[
 f_R=\chi_Rf,\qquad
 g_{R,k}=\chi_Rg_k+(D_k\chi_R)f.                              \tag{9}
\]
Testing (8) with \(\chi_R\phi\) proves the weak product rule. All products
are L², and
\[
 \|f_R-f\|_2\to0,\qquad
 \|g_{R,k}-g_k\|_2
 \le\|(\chi_R-1)g_k\|_2+C_1R^{-1}\|f\|_2\to0.                \tag{10}
\]
For H² inputs, a second weak product rule gives
\[
 e_{R,kl}=\chi_Re_{kl}+(D_l\chi_R)g_k+(D_k\chi_R)g_l
                         +(D_lD_k\chi_R)f,                 \tag{11}
\]
whose difference from \(e_{kl}\) has norm at most
\[
 \|(\chi_R-1)e_{kl}\|_2+
 C_1R^{-1}(\|g_k\|_2+\|g_l\|_2)+C_2R^{-2}\|f\|_2\to0.
\]
No prior equality of mixed derivative witnesses is required for this step.

Take a nonnegative compact smooth mollifier \(\rho\) of integral 1 and put
\(\rho_h(x)=h^{-3N}\rho(x/h)\). For fixed \(R\),
\[
 f_{R,h}=\rho_h*f_R\in C_c^\infty,\quad
 D_kf_{R,h}=\rho_h*g_{R,k},\quad
 D_lD_kf_{R,h}=\rho_h*e_{R,kl}.                               \tag{12}
\]
Insert the translated mollifier in (8) to prove the first identity; repeat
with \(g_{R,k},e_{R,kl}\) for the second. The smooth compact kernels and L²
factors justify the integrations. Approximate-identity convergence in L²
applies to each of this finite collection of functions. It follows from
translation continuity in L² and
\[
 \|\rho_h*v-v\|_2
 \le\int\rho(y)\|v(\,\cdot-hy)-v\|_2\,dy.
\]
Translation continuity can be proved using ordinary continuous compact
support density in L², without presupposing Sobolev density. A diagonal
choice \(R\to\infty,\ h\to0\) gives compact smooth approximation in all the
actual H¹ or H² derivative norms. Such mathematical diagonal selection is
not asserted to be an executable approximation algorithm.

For H¹ approximants \(f_m\to f\), extract a subsequence converging a.e.
Multiplication by each fixed totalized reciprocal preserves this pointwise
convergence. Fatou in (5), and convergence of the derivative norms, give
\[
 \|f/|x_i|\|_2^2\le4\sum_\alpha\|g_{i,\alpha}\|_2^2.           \tag{13}
\]
Apply the same argument to (6) and (7); derivative differences converge in
L² as well. Measurable products and finite square integrals yield MemLp.
Thus all bounds extend without invoking weak slicing.

The existing SmoothL2Density_v2.lean is ordinary L² density, not by itself
the derivative-norm convergence in (10)–(12). The weak cutoff and convolution
modules cover parts of this argument; their exact successful statements
determine what is formally complete. The smooth core must be allowed to
cross collision sets: vanishing near codimension-three collisions is not
generally dense in H² because trace constraints can persist.

## 5. Finite-spin Coulomb constants and graph membership

For every scalar H¹ input and \(i\ne j\), the representative conclusions are

~~~lean
MemLp (fun x => f x / (‖position x i‖ : ℂ)) 2 volume
MemLp (fun x => f x / (‖position x i - position x j‖ : ℂ)) 2 volume
~~~

Finite sums and scalar multiplication then give exactly

~~~lean
MemLp (fun x => (coulombPotential N Z x : ℂ) * f x) 2 volume
~~~

Division and reciprocal multiplication agree under the totalized field
conventions. The pair sum is over \(i<j\), not ordered distinct pairs.

After the spin square sum, set
\[
 H_{ij}^2=\sum_{\sigma,\alpha}
   \|D_{i,\alpha}\psi_\sigma-D_{j,\alpha}\psi_\sigma\|_2^2,
 \qquad M=N(N-1)/2 .
\]
Then
\[
 \|V\psi\|\le2|Z|\sum_iG_i+\sum_{i<j}H_{ij}.
\]
The complete-graph identity in the derivative Hilbert space is
\[
 \sum_{i<j}H_{ij}^2
 =N\sum_iG_i^2-\sum_{\sigma,\alpha}
                   \|\sum_iD_{i,\alpha}\psi_\sigma\|_2^2
 \le NG^2.
\]
Finite Cauchy–Schwarz therefore gives
\[
 \boxed{\ \|V\psi\|\le C_{N,Z}G,\qquad
 C_{N,Z}=2|Z|\sqrt N+\sqrt{NM}.\ }                            \tag{14}
\]
The translation route alone gives
\[
 \|V\psi\|\le\sqrt N(2|Z|+N-1)G\quad(N\ge1),                 \tag{15}
\]
which matches the proposed specification for \(Z\ge0\). Formula (14) improves
the pair term for \(N>2\), without claiming an optimal constant.

GraphAssembly_v2.lean already gives
scalar_graph_exists_of_coulombProductL2 from actual HasH2 and this MemLp
fact. Consequently H¹ Hardy extension plus the finite Coulomb sum supplies
the analytic input to that graph-existence implication. Fermionic output
preservation requires the separate simultaneous-permutation proof. No
not-yet-composed implication is silently counted as completed here.

## 6. Fourier convention and compact-test distribution bridge

The pinned revision is mathlib d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9,
with Lean leanprover/lean4:v4.34.0-rc2. Mathlib uses
\[
 \widehat f(\xi)=\int e^{-2\pi i\langle x,\xi\rangle}f(x)\,dx,
 \qquad\|\widehat f\|_2=\|f\|_2.                              \tag{16}
\]
For general L² functions this denotes the unitary extension, not an
absolutely convergent integral. Its multipliers are
\[
 \widehat{D_kf}=2\pi i\xi_k\widehat f,\qquad
 \widehat{\Delta f}=-(2\pi)^2|\xi|^2\widehat f,\qquad
 \widehat{(-\Delta/2)f}=2\pi^2|\xi|^2\widehat f.                \tag{17}
\]
The earlier continuum paper instead used the equally valid unitary
\((2\pi)^{-3N/2}e^{-ix\cdot\xi}\) convention. Those multiplier coefficients
must not be copied unchanged into this Lean environment.

The distribution pairing in mathlib is **bilinear**, with no conjugation:
\[
 \iota(f)(\phi)=\int\phi f,\qquad D_kT(\phi)=-T(D_k\phi).
\]
The exact interface required for the existing project domain is
\[
 \operatorname{WeakPartial}(f,g,k)
 \quad\Longleftrightarrow\quad
 D_{e_k}\iota(f)=\iota(g).                                   \tag{18}
\]
For the forward direction, first extend the real compact test identity to
complex compact tests by real and imaginary parts. Given a Schwartz test
\(\phi\), use \(\chi_R\phi\). Then
\[
 \|\chi_R\phi-\phi\|_2\to0,\qquad
 \|D_k(\chi_R\phi)-D_k\phi\|_2
 \le\|(\chi_R-1)D_k\phi\|_2+C_1R^{-1}\|\phi\|_2\to0.
\]
Cauchy–Schwarz passes the identity to the limit against \(f,g\in L^2\).
Only the test was approximated; this argument needs no H¹/H² density of
the wavefunction. Ordinary L² density of tests alone would be insufficient,
because the functional involving \(D_k\phi\) is not L²-continuous.
For the reverse direction, a smooth compact test is Schwartz by
HasCompactSupport.toSchwartzMap. Evaluate the distribution equality on its
complexification, noting that complexification commutes with real
differentiation.

The corresponding weak-Laplacian bridge is
\[
 \int\phi w=\int(\Delta\phi)f\quad\text{for all real compact smooth }\phi
 \quad\Longleftrightarrow\quad\Delta\iota(f)=\iota(w).          \tag{19}
\]
Its sign is positive before Fourier transformation. The same cutoff proof
works with second derivatives of \(\chi_R\phi\): errors are \(O(R^{-1})\)
times first test derivatives and \(O(R^{-2})\) times the test, all in L².

The existing APIs include MeasureTheory.Lp.fourierTransformₗᵢ,
Lp.norm_fourier_eq, Lp.inner_fourier_eq,
Lp.fourier_toTemperedDistribution_eq,
TemperedDistribution.fourier_lineDerivOp_eq, and
TemperedDistribution.laplacian_eq_fourierMultiplierCLM. The missing project
interface is (18)–(19), not another construction of the L² Fourier transform.

## 7. Two noncircular routes from an L² weak Laplacian to actual H²

**Bessel-potential domain route.** Mathlib's order-s Bessel potential \(J_s\)
has symbol \((1+|\xi|^2)^{s/2}\). Therefore on tempered distributions,
\[
 J_2T=T-(2\pi)^{-2}\Delta T.                                \tag{20}
\]
This is addition of the constant and squared-norm Fourier multipliers.
For \(f,w\in L^2\) with \(\Delta\iota(f)=\iota(w)\), the explicit L² element
\(f-(2\pi)^{-2}w\) witnesses MemSobolev 2 2 of \(\iota(f)\).
Existing MemSobolev.lineDerivOp lowers the order by one, MemSobolev.mono
lowers it further, and memSobolev_zero_iff extracts an L² representative.
These yield L² representatives \(g_k\) and \(e_{kl}\) of the first and ordered
second distribution derivatives. The reverse direction of (18) gives
precisely the existing HasH2 witnesses.

Thus domain membership can be obtained without an unbounded pointwise
multiplier API. The actual compact-test/distribution bridge must still be
implemented and audited. A new distribution-level Lean lemma with hypothesis
\(\Delta\iota(f)=\iota(w)\) does not by itself complete physical graph
existence, self-adjointness, or spectral identification.

**Pointwise Fourier route.** The theorem
Lp.toTemperedDistribution_smul_eq assumes MemLp of the multiplier itself at
a Hölder exponent. It cannot be applied directly to global coordinate or
squared-norm polynomials, which are neither bounded nor in any finite Lp
space on positive-dimensional Euclidean space.

Use local distribution uniqueness instead. For \(h\in L^2\) and a polynomial
\(m\), \(mh\) is locally integrable because \(m\) is bounded on compact sets.
If \(k\in L^2\) and
\[
 \operatorname{smulLeftCLM}(m,\iota(h))=\iota(k),
\]
evaluation on compact smooth real tests gives \(\int\phi mh=\int\phi k\).
The existing ae_eq_of_integral_contDiff_smul_eq then yields \(mh=k\) a.e.
**Only after this identification** transfer MemLp from \(k\) to \(mh\).
Conversely, if the product is already L², equality of its distribution
embedding with smulLeftCLM follows by integral_congr_ae on Schwartz tests
and the identity \((m\phi)h=\phi(mh)\). This converse requires MemLp of the
product, not of the multiplier. It does not assert that every polynomial
preserves L².

Fourier/distribution compatibility and (19) therefore give
\[
 -(2\pi)^2|\xi|^2\widehat f(\xi)=\widehat w(\xi)\ \text{a.e.},
 \qquad |\xi|^2\widehat f\in L^2.                             \tag{21}
\]
The first and second products in (17) are now L² because
\(|\xi_k|\le1+|\xi|^2\) and \(|\xi_k\xi_l|\le|\xi|^2\).
Inverse L² Fourier transforms provide the derivative witnesses. The
product-embedding principle, Fourier injectivity, and (18) identify them as
the actual weak derivatives. Conversely, HasH2 supplies
\(w=\sum_ke_{kk}\in L^2\); applying (8) twice gives (19). Hence the exact
paper equivalence is
\[
 f\in H^2_{\rm weak}
 \iff\exists w\in L^2:\Delta\iota(f)=\iota(w)
 \iff|\xi|^2\widehat f\in L^2.                               \tag{22}
\]
No eigenfunction, attainment, binding, or spectral assumption is used.

## 8. Laplacian interpolation with all constants accounted for

For the actual H² witnesses, Plancherel and (17), followed by integral
Cauchy–Schwarz, give
\[
 \sum_k\|D_kf\|_2^2
 =(2\pi)^2\int|\xi|^2|\widehat f|^2
 \le\|f\|_2\|\Delta f\|_2.                                  \tag{23}
\]
All \(2\pi\) factors cancel against the norm of the Laplacian. Moreover,
\[
 \sum_{k,l}\|D_lD_kf\|_2^2
 =(2\pi)^4\int\bigl(\sum_{k,l}\xi_k^2\xi_l^2\bigr)|\widehat f|^2
 =\|\Delta f\|_2^2.                                         \tag{24}
\]
The sum is over **ordered pairs**, counting mixed entries twice, exactly as
in HasH2. Counting each mixed derivative just once changes this identity.
Alternatively (23) follows by integration by parts and the H² density
argument in §4, providing a separate real-variable route to the estimate.

Summing (23) over spin and applying Cauchy–Schwarz in spin gives
\(G^2\le\|\psi\|\|\Delta\psi\|\), with no spin-counting factor.
For \(A=-\Delta/2\), (14) and scalar Young's inequality yield, for every
\(\varepsilon>0\),
\[
 \boxed{\ \|V\psi\|
   \le C_{N,Z}\sqrt{2\|\psi\|\|A\psi\|}
   \le\varepsilon\|A\psi\|
       +\frac{C_{N,Z}^2}{2\varepsilon}\|\psi\|.\ }             \tag{25}
\]
Dependence on N and Z is explicit. This is the infinitesimal-relative-bound
input to the actual Coulomb operator proof; it alone is not formal
self-adjointness or spectral/variational equality, and says nothing about
operational bit complexity.

## 9. Concrete formal interfaces and source evidence

1. Compact configuration Hardy: (3)–(5), then translated pair Hardy (6).
2. Actual H¹ cutoff/mollifier convergence and Fatou: (9)–(13).
3. Finite Coulomb MemLp sum, existing scalar graph existence, and the
   separate fermionic preservation implication.
4. Actual WeakPartial/distribution bridge (18), with its reverse direction
   independently available from compact-to-Schwartz.
5. Bessel identity (20) and the existing Sobolev derivative lemmas for exact
   H² domain membership; pointwise Fourier identification or weak
   integration by parts for (23)–(25).

This list describes the precise remaining work; it is not evidence that all
five steps are already formalized. The inspected primary source is the
pinned local mathlib checkout. No novelty is claimed for the standard
analytic facts or the source APIs.

| Source below formal/.lake/packages/mathlib/ | SHA-256 |
| --- | --- |
| Mathlib/Analysis/Fourier/LpSpace.lean | 29fa367dd88808d8537cb013e01e3e967af8fe1c34aa19e19abd1c7f71d8448e |
| Mathlib/Analysis/Distribution/TemperedDistribution.lean | ecec97390a5f9743be566537c4e09f6d9e337a341dd771f9b799835405786a98 |
| Mathlib/Analysis/Distribution/FourierMultiplier.lean | cf095354a791fddbf35bc75cca5dd9e345977d491c4931fdc819c8bdd91d8184 |
| Mathlib/Analysis/Distribution/Sobolev.lean | ddf3e23d6c1b43a63d46264f730334b0ea8b1118a9e074816f772e79481975b5 |
| Mathlib/Analysis/Distribution/AEEqOfIntegralContDiff.lean | 626e88cc762fe508d78e07923fdb29ab8b5c47e932b30e43e3cc352c0fee9eb2 |
