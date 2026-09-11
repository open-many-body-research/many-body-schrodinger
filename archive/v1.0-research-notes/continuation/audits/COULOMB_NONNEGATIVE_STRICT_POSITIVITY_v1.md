> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Strict positivity through all Coulomb collisions

Evidence category: **paper theorem** for an existing actual scalar weak-H2
eigenfunction. No ground-state attainment, eigenvalue isolation, or formal
verification is asserted.

## 1. Actual hypothesis and conclusion

Let \(N\ge1\), \(Z\ge0\), and \(E\in\mathbb R\). On
\(\mathbb R^d\), \(d=3N\), use the physical scalar Hamiltonian
\[
 H=-\tfrac12\Delta-Z\sum_i|x_i|^{-1}
                       +\sum_{i<j}|x_i-x_j|^{-1}.
\]
Suppose \(0\ne\psi\in H^2(\mathbb R^d;\mathbb C)\) satisfies
\(H\psi=E\psi\) in L2, and \(\psi\) is real and nonnegative almost
everywhere. Then its canonical locally Lipschitz representative satisfies
\[
                 \boxed{\ \psi(x)>0\quad(x\in\mathbb R^d).\ }       \tag{P1}
\]
The conclusion includes every collision set and their intersections.
For example \(\psi(0)>0\). This is a qualitative strict positivity
statement, not a computable positive lower bound from \(N,Z,E\) alone.

The input is scalar. A nonzero vector in a spin space has no analogous
componentwise strict positivity conclusion without a separate scalar
factorization. The spin-singlet use is specified in section 6.

## 2. Bounded-coefficient equation and a C1 representative

Use the actual cusp factor and constants
\[
 F=-Z\sum_i|x_i|+\tfrac12\sum_{i<j}|x_i-x_j|,\quad
 A_F=Z\sqrt N+\frac{N(N-1)}{2\sqrt2},\quad
 \phi=e^{-F}\psi .
\]
The sealed local Lipschitz theorem establishes the weak product rule,
\(\phi\in H^2_{\rm loc}\cap W^{1,\infty}_{\rm loc}\), and
\[
 \Delta\phi=-2b\cdot\nabla\phi-c\phi,\qquad
 b=\nabla F,\quad c=|b|^2+2E,\quad
 |b|\le A_F,\quad |c|\le C_0:=A_F^2+2|E|.                       \tag{P2}
\]
The regularity statement holds on every finite ball by taking the
radius parameter large enough. Its representatives agree on overlaps.
Since \(F\) is real and continuous, \(\phi\) has a continuous nonnegative
representative and is nonzero. Equation (P2) holds through the collision
sets in distributions; coefficients on null sets can be assigned
arbitrary bounded values.

Here the bounded right side upgrades \(\phi\) to C1 locally without a
Calderon–Zygmund or Harnack input. Fix any two concentric balls
\(B_r\Subset B_R\), with any common center, and a smooth cutoff
\(\eta=1\) near \(\overline{B_r}\), compactly supported in \(B_R\).
Then \(z=\eta\phi\) is compactly supported H2 and
\[
 f=\Delta z=\eta\Delta\phi+2\nabla\eta\cdot\nabla\phi+
                        (\Delta\eta)\phi
\]
is bounded and compactly supported. With
\(\Gamma(x)=-|x|^{2-d}/((d-2)\omega_d)\), the compact-support
distribution identity already proved in the Lipschitz theorem gives
\[
                  \nabla z=(\nabla\Gamma)*f.                   \tag{P3}
\]
There is no harmonic remainder: \(\Gamma*\Delta z=(\Delta\Gamma)*z=z\).

For \(x\) in a fixed neighborhood of \(\overline{B_r}\), every
displacement \(x-y\) with \(y\in\operatorname{supp}f\) lies in a fixed
ball \(B_D(0)\). The vector kernel
\(K=(\nabla\Gamma)\mathbf1_{B_D(0)}\) belongs to L1, since its
radial absolute integral near zero is a constant times
\(\int_0^D1\,dt\). On that neighborhood, the right side of (P3)
equals \(K*f\). It is continuous, because
\[
 \|(K*f)(\,\cdot+h)-(K*f)\|_\infty
       \le\|\tau_hK-K\|_1\|f\|_\infty\longrightarrow0.           \tag{P4}
\]
For completeness, L1 translation continuity follows by choosing a
continuous compactly supported approximation to \(K\) in L1;
translations preserve the L1 error, while the approximation is uniformly
continuous on a common compact support. Such approximations follow
from truncation and approximation of integrable simple functions,
or ordinary mollification after truncation.

Thus the weak gradient of \(\phi\) has a continuous representative
locally. Mollify \(\phi\) on a slightly smaller ball. The functions
converge uniformly to its Lipschitz representative, and their gradients
converge uniformly to that continuous weak gradient on compact subsets.
Passing the fundamental theorem of calculus on a segment to the
limit proves differentiability with this gradient. Hence
\[
                         \phi\in C^1(\mathbb R^d).             \tag{P5}
\]
This does not assert that \(\psi=e^F\phi\) is C1 across a Coulomb cusp.

## 3. Weak comparison on an explicitly small annulus

Set \(B(x)=2b(x)\), \(B_0=2A_F\), and define
\[
              \mathcal L v=\Delta v+B(x)\cdot\nabla v-C_0v.
\]
Equation (P2), nonnegativity, and \(c+C_0\ge0\) show
\[
                         \mathcal L\phi\le0.                  \tag{P6}
\]

We will only need the following comparison statement. Let
\[
 A=\{x:R/2<|x-y|<R\},\qquad
                    0<R<\frac1{4(1+B_0)}.                   \tag{P7}
\]
Suppose \(v\) is Lipschitz on a neighborhood of \(\overline A\),
\(\mathcal Lv\le0\) distributionally in \(A\), and \(v\ge0\) on
both boundary spheres. Then \(v\ge0\) on \(A\).

Indeed \(w=v_-=\max(-v,0)\) is Lipschitz and zero on the boundary.
It belongs to \(H^1_0(A)\). One direct verification cuts it off
within distance \(\varepsilon\) of the boundary: the term from
the cutoff gradient is bounded by a constant times the Lipschitz
constant on this shrinking layer because
\(|w|\le\operatorname{Lip}(w)\operatorname{dist}(x,\partial A)\).
Its L2 norm tends to zero with the layer volume, as does the omitted
gradient. Mollifying these inner cutoffs proves H1 approximation
by compact smooth functions. Nonnegative approximants may be used.

Test \(\mathcal Lv\le0\) with \(w\). Bounded coefficients and the
H1 approximation justify this test; the chain rule for the negative
part gives
\[
 \|\nabla w\|_2^2+C_0\|w\|_2^2
              \le\int_A B\cdot\nabla w\,w
              \le B_0\|\nabla w\|_2\|w\|_2.                   \tag{P8}
\]
To see the sign, the distributional Laplacian contributes
\(-\int\nabla v\cdot\nabla w=\|\nabla w\|_2^2\), while the drift
contributes \(-\int B\cdot\nabla w\,w\).

Extend \(w\) by zero to the cube of side \(2R\) centered at \(y\).
The one-dimensional fundamental theorem of calculus along the
first coordinate, followed by Cauchy–Schwarz and integration, gives
\[
                         \|w\|_2\le2R\|\nabla w\|_2.           \tag{P9}
\]
It first applies to compact smooth functions and then to the H1
extension. Thus (P8) implies
\(\|\nabla w\|_2^2\le2RB_0\|\nabla w\|_2^2\), with
\(2RB_0<1/2\) by (P7). Therefore \(w=0\). Continuity proves the
pointwise comparison statement. Neither differentiability nor
a divergence bound for the measurable vector field \(B\) is used.

## 4. An explicit barrier

On the annulus (P7), put
\[
 \lambda=\max\left(1,\frac{8d}{R^2},\frac{8B_0}{R},
                                      \frac{2\sqrt{C_0}}R\right),
 \qquad W(x)=e^{-\lambda|x-y|^2}-e^{-\lambda R^2}.              \tag{P10}
\]
Then \(0\le W\le1\), and \(W=0\) on the outer sphere. Writing
\(r=|x-y|\), direct differentiation gives almost everywhere
\[
 \begin{aligned}
 \mathcal LW
 &\ge e^{-\lambda r^2}
           (4\lambda^2r^2-2\lambda d-2\lambda B_0r-C_0)\\
 &\ge e^{-\lambda r^2}
           (\lambda^2R^2-2\lambda d-2\lambda B_0R-C_0)\\
 &\ge\tfrac14\lambda^2R^2e^{-\lambda r^2}>0.                  \tag{P11}
 \end{aligned}
\]
The last line uses three separate inequalities:
\(2\lambda d\le\lambda^2R^2/4\),
\(2\lambda B_0R\le\lambda^2R^2/4\), and
\(C_0\le\lambda^2R^2/4\). The zeroth-order estimate uses
\(-C_0W\ge-C_0e^{-\lambda r^2}\). Because the leading coefficient
is constant, these pointwise almost-everywhere inequalities also
give the distributional inequality needed for section 3.

## 5. Exclusion of an interior zero

Suppose the closed zero set \(Z_\phi=\{x:\phi(x)=0\}\) is nonempty.
The open positive set is also nonempty. A line segment joining
a positive point to a zero point shows that positive points can
be chosen arbitrarily close to \(Z_\phi\). Choose such a point
\(y\) so that
\[
              R=\operatorname{dist}(y,Z_\phi)>0
                  \quad\hbox{satisfies (P7).}
\]
The distance is attained at some \(z_0\in Z_\phi\), since a
minimizing sequence lies in a bounded closed ball in finite
dimension. The whole ball \(B_R(y)\) is positive. Consequently
\[
                    m=\min_{|x-y|=R/2}\phi(x)>0.
\]
With \(\varepsilon=m/2\), the function
\(v=\phi-\varepsilon W\) is nonnegative on the inner sphere
because \(W\le1\), and on the outer sphere because \(W=0\).
Equations (P6) and (P11) imply \(\mathcal Lv\le0\). It is
Lipschitz on a neighborhood of the annulus closure by (P5).
The comparison statement proves
\[
                       \phi\ge\varepsilon W\quad\hbox{on }A.
\]
Let \(\nu=(z_0-y)/R\). For sufficiently small \(t>0\),
\(z_0-t\nu\in A\), and hence
\[
 \frac{\phi(z_0-t\nu)-\phi(z_0)}{t}
 \ge\varepsilon
       \frac{e^{-\lambda(R-t)^2}-e^{-\lambda R^2}}t
 \longrightarrow 2\varepsilon\lambda R e^{-\lambda R^2}>0.    \tag{P12}
\]
But \(z_0\) is a nonnegative minimum of the C1 function \(\phi\)
at an interior point of \(\mathbb R^d\). Thus
\(\nabla\phi(z_0)=0\), contradicting (P12). The zero set is empty.
Since \(e^F>0\) everywhere, (P1) follows.

## 6. Precise spectral and fermionic use

SCALAR_GROUND_FERMIONIC_COMPARISON_v1.md proves, under its explicit
actual scalar self-adjointness, simple bottom attainment and form
hypotheses, that the bottom has a real nonnegative normalized
actual-H2 representative \(\psi\), invariant under simultaneous
spatial rotations and electron exchange. Applying the present
theorem then makes that scalar representative strictly positive,
including at the simultaneous collision.

For two electrons the spin-singlet vector
\(\Psi=\psi\otimes\chi_{\rm singlet}\) is the corresponding actual
full fermionic vector, as proved in that separate comparison.
The signs of the two nonzero spin components remain opposite;
we do not call the full spin vector componentwise positive.
The conclusion \(\psi(0)>0\) supplies the meaning of the scalar
collision value used by the physical distance-analytic expansion.

This theorem neither constructs the eigenfunction nor proves
that a given scalar spectral infimum is attained or simple.
It does not remove the spectral prerequisites of that comparison.

## 7. Evidence and preservation

This is a self-contained bounded-coefficient strong-minimum
argument after the already proved cusp transformation. It is
a classical mechanism, not a novelty claim. The proof gives
the exact comparison radius and barrier parameter, but its
positive number \(m\) depends on the existing solution; no
certified procedure for that number is claimed.

| Dependency | SHA-256 |
|---|---|
| COULOMB_LOCAL_LIPSCHITZ_v1.md | 4429fa7abefc10fc9c0f2c6f3c8c94bf44b424b8c2208539da10017c700d8a78 |
| COULOMB_GLOBAL_BOUNDEDNESS_v1.md | d103aa471fcb626ca330d02a4cfbc6534a038e8827e129cff6c24ef3351377a7 |
| SCALAR_GROUND_FERMIONIC_COMPARISON_v1.md | 605b1a0261a74f00d4181c193ffe8515b6a5ee8f4e41eeefcf6b3c02e59fd841 |

Only the first dependency and its proved prerequisites are needed
for (P1); the scalar comparison is used only in section 6.
Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The frozen downstream physical scalar-state target is
rwa_proof/RWA_THEOREM.md, SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
All new work is in the versioned continuation. No frozen or
sealed successful artifact was modified. No Lean claim is made.

