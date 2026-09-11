> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent check of the two-electron product trial

Evidence category: direct paper calculation on the actual weak operator domain.
This verifies a trial mean and a scalar comparison inequality; it does not
establish a complementary spectral lower bound, binding, ground simplicity,
or full Theorem T. No frozen artifact is changed.

## 1. Trial, normalization, and actual domain

For alpha > 0 put

\[
 f_\alpha(x)=(\alpha^3/\pi)^{1/2}e^{-\alpha|x|},\qquad
 \Phi_\alpha(x,y)=f_\alpha(x)f_\alpha(y)
                 =(\alpha^3/\pi)e^{-\alpha(|x|+|y|)}.
\]

The identity integral_0^infinity t^n exp(-b t) dt = n!/b^(n+1),
for nonnegative integers n and b > 0, follows by integration by parts.
It gives

\[
 \|f_\alpha\|_2^2=4\alpha^3\frac{2}{(2\alpha)^3}=1,
 \qquad \|\Phi_\alpha\|_2=1.
\]

For r = |x| > 0 its first and second derivatives are

\[
 \partial_i f_\alpha=-\alpha\frac{x_i}{r}f_\alpha,
 \quad
 \partial_j\partial_i f_\alpha
 =\left[\alpha^2\frac{x_i x_j}{r^2}
       -\alpha\left(\frac{\delta_{ij}}r-
                         \frac{x_i x_j}{r^3}\right)\right]f_\alpha.
\]

These formulas are also weak derivatives on R^3. Integrating against a
compact smooth test function outside a radius-epsilon ball, the boundary
term for the first derivative and that for differentiating the bounded
first derivative are O(epsilon^2), hence vanish. In particular there is no
delta measure at the cusp. The Hessian entries have magnitude at most
(alpha^2 + 2 alpha/r) f_alpha; their squares are integrable since
r^2 dr cancels r^(-2) near zero and the exponential controls infinity.
Thus f_alpha belongs to actual H^2(R^3). The pure second derivatives of
Phi_alpha are tensor products of these derivatives and f_alpha, and its
mixed x,y second derivatives are products of first derivatives. Fubini
therefore proves Phi_alpha belongs to actual H^2(R^6).

The nuclear Coulomb products are in L^2 by the same radial integrability.
For the pair term use u = x-y, v = (x+y)/2, a linear change with absolute
Jacobian one. Since |x|+|y| >= |u| and >= 2|v|, it is >= |u|/2 + |v|.
Consequently the square of Phi_alpha/|x-y| is bounded by a constant times
|u|^(-2) exp(-alpha|u|) exp(-2 alpha|v|), an integrable function on R^6.
The literal expression

\[
 H_Z=-\tfrac12(\Delta_x+\Delta_y)
       -Z/|x|-Z/|y|+1/|x-y|
\]

therefore maps this actual H^2 trial to L^2. This domain check does not
require the trial to satisfy an eigenfunction cusp condition.

## 2. Direct angular and radial pair integral

For r,s > 0, rotational invariance and t = cos(theta) give

\[
 \int_{S^2}\frac{d\omega}{|r\omega-s\eta|}
 =2\pi\int_{-1}^1\frac{dt}{\sqrt{r^2+s^2-2rs t}}
 =\frac{2\pi}{rs}(r+s-|r-s|)
 =\frac{4\pi}{\max(r,s)}.
\]

The endpoint at r=s is integrable. Integrating over eta in S^2 gives
16 pi^2/max(r,s). Positivity permits every following order exchange by
Tonelli. With k = 2 alpha and J denoting the pair mean,

\[
\begin{aligned}
 J&=16\alpha^6\int_0^\infty\!\int_0^\infty
        \frac{r^2s^2 e^{-k(r+s)}}{\max(r,s)}\,ds\,dr\\
  &=32\alpha^6\int_0^\infty s^2e^{-ks}
                  \left(\int_s^\infty r e^{-kr}\,dr\right)ds\\
  &=32\alpha^6\left[
       \frac1k\frac{3!}{(2k)^4}
       +\frac1{k^2}\frac{2!}{(2k)^3}\right]
    =\frac{20\alpha^6}{k^5}=\frac{5\alpha}{8}.
\end{aligned}
\]

Here the inner tail integral is exp(-ks)(s/k + 1/k^2). The diagonal r=s
has measure zero and introduces no factor beyond the displayed factor two.

## 3. Exact mean and optimized comparison

The first derivative formula gives ||grad f_alpha||_2^2 = alpha^2.
Also integral |f_alpha(x)|^2/|x| dx = alpha. Thus actual integration by
parts, justified by the H^2 domain, yields the exact normalized mean

\[
 \mu_Z(\alpha)=\langle\Phi_\alpha,H_Z\Phi_\alpha\rangle
       =\alpha^2-2Z\alpha+\frac{5\alpha}{8}
       =\left(\alpha-Z+\frac5{16}\right)^2
                            -\left(Z-\frac5{16}\right)^2.
\]

When Z > 5/16, the unique positive minimizer is alpha_* = Z-5/16,
with mu_* = -(Z-5/16)^2. When Z <= 5/16, the infimum over alpha > 0
is zero and is not attained. Write beta_Z = -5Z^2/8. For Z > 5/16,

\[
 \mu_*<\beta_Z
 \iff 96Z^2-160Z+25>0
 \iff Z>\frac{20+5\sqrt{10}}{24}.
\]

Indeed the quadratic roots are (20 +/- 5 sqrt(10))/24, and the lower
root is less than 5/16, so it is excluded by the positive-optimizer
condition. For Z <= 5/16, every positive-alpha mean is positive while
beta_Z <= 0. Hence even the existence statement is exact for real Z:
there is alpha > 0 with mu_Z(alpha) < beta_Z if and only if
Z > (20+5 sqrt(10))/24. Equality at the upper threshold gives no strict
inequality for any alpha. In particular every integer Z >= 2 qualifies.
For Z = 2, alpha_* = 27/16, mu_* = -729/256, beta_Z = -640/256,
and beta_Z-mu_* = 89/256.

## 4. Full fermionic spin realization and limit of the conclusion

Let chi(up,down) = 1/sqrt(2), chi(down,up) = -1/sqrt(2), and let the
equal-spin components vanish. Then Psi_alpha,sigma = Phi_alpha chi_sigma
has four actual H^2 components, norm one, and changes sign under
simultaneous exchange of positions and spin labels. It is therefore in
the full two-electron fermionic operator domain and is a spin singlet.
The spin-independent Hamiltonian acts componentwise, so its mean is
exactly mu_Z(alpha), with no spin multiplicity factor.

The variational principle supplies E_ferm <= mu_Z(alpha) for the actual
self-adjoint fermionic realization. The number beta_Z has only been
compared algebraically with this mean here; this calculation alone does
not prove that beta_Z separates the ground eigenspace from its complement.
A hydrogenic comparison and the necessary spectral arguments remain
separate dependencies. No scalar attainment, positivity, or uniqueness
claim is assumed or proved in this audit.

## 5. Frozen provenance

Historical target: frozen relative path `rwa_proof/RWA_THEOREM.md`,
Section 1, lines 10-16, in `THEOREM_T_FREEZE_2026-09-09_212604/`.
SHA-256: `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`.
The frozen manifest digest and the actual file digest were checked equal.
Commit: `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`.
Tag: `theorem-t-proof-freeze-2026-09-09`.

Preservation protocol: frozen relative path `CORRECTION_PROTOCOL.md`,
SHA-256 `1bdb5c1b27de5eaf21b635b08581131c84f4436cff342b45f67fae8f82db2bb3`
(manifest and actual file agree), under the same snapshot, commit and tag.
This is a new independent verification, not an alteration or validation
of the frozen theorem's other assertions. The formulas were derived
above directly, without numerical reference energies or external sources.
