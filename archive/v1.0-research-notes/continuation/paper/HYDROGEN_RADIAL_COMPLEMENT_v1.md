> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# The sharp half-line hydrogen complement bound

Evidence category: **paper proof**, not a Lean verification. This file proves
a concrete half-line form inequality with every operator domain specified.
Its use in the full three-dimensional scalar hydrogen problem additionally
requires the angular and radial decomposition proved in a separate file.
No radial self-adjoint realization or adjoint-domain identification is assumed.

Frozen provenance: `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. All files created here are new; frozen and
previously successful artifacts are unchanged.

## 1. Statement and precise spaces

Fix a real `Z > 0`. Let `K = L²((0,∞),dr;ℂ)` with inner product

\[
\langle f,h\rangle=\int_0^\infty\overline{f(r)}h(r)\,dr,
\]

linear in the second argument. Let `H¹(0,∞)` mean actual weak Sobolev H¹,
and let `D = H¹₀(0,∞)` be the closure of `C_c^∞(0,∞;ℂ)` in its H¹ norm.
Section 2 verifies the equivalent zero-trace description and the approximation
facts used below. Put

\[
g_Z(r)=r e^{-Zr},\qquad
q_Z[u]=\frac12\|u'\|_2^2-Z\int_0^\infty\frac{|u(r)|^2}{r}\,dr.
\tag{1.1}
\]

The integral is finite for every `u∈D`, by the proved half-line Hardy
inequality in Section 3.

**Theorem R.** For every `u∈D` satisfying `⟨g_Z,u⟩=0`,

\[
\boxed{q_Z[u]\ge-\frac{Z^2}{8}\|u\|_2^2.}
\tag{1.2}
\]

The constant is optimal. Equality holds precisely for the complex multiples
of

\[
u_{2,Z}(r)=r\left(1-\frac{Zr}{2}\right)e^{-Zr/2}.
\tag{1.3}
\]

In particular this is a bound on the entire form-domain complement, not
only on compact tests, eigenfunctions, or a presumed spectral basis.

For `ĝ_Z=g_Z/‖g_Z‖₂`, the following equivalent rank-one form comparison holds
for every `u∈D`:

\[
\boxed{q_Z[u]\ge-\frac{Z^2}{8}\|u\|_2^2
 -\frac{3Z^2}{8}|\langle\widehat g_Z,u\rangle|^2.}
\tag{1.4}
\]

All conclusions concern complex functions. Orthogonality with the arguments
reversed is equivalent, by conjugate symmetry.

## 2. Weak H¹, zero trace, and compact approximation

Weak H¹ is complete. Indeed, if `u_j` and their weak derivatives `u_j'`
are Cauchy in L², let their limits be `u,w`. Passing the compact-test weak
derivative equation to the limit by Cauchy–Schwarz gives `u'=w`. Thus H¹
is the closed derivative graph in `K×K`; its closed subspace D is complete.

We record the elementary one-dimensional representative fact used here.
If `u,w∈L²(a,b)` and `u'=w` weakly, the function
`F(x)=∫_{x₀}^x w(t)dt` is absolutely continuous, and `u−F` has zero
distributional derivative. A distribution with zero derivative on an
interval is constant: a smooth compact test with integral zero is the
derivative of a smooth compact test, and subtracting a fixed test of
integral one reduces every test to that case. Therefore `u` has the
absolutely continuous representative `c+F`.

Applied on intervals contained in `(0,∞)`, these representatives agree on
overlaps. Moreover

\[
|u(t)-u(s)|\le\sqrt{|t-s|}\,\|u'\|_{L^2(s,t)}
\quad(0<s<t),
\tag{2.1}
\]

so the representative has a finite limit `u(0)` as `t↓0`. Integrating
`|u(0)|≤|u(t)|+∫₀¹|u'|` over `0<t<1` shows

\[
|u(0)|\le\|u\|_{L^2(0,1)}+\|u'\|_{L^2(0,1)}.
\tag{2.2}
\]

Thus the trace is continuous and every member of D has zero trace.

Conversely suppose `u∈H¹(0,∞)` and `u(0)=0`. Then
`u(r)=∫₀^r u'(t)dt` and `|u(r)|²≤r∫₀^r|u'|²`. Choose the Lipschitz cutoff
`η_ε`, zero on `[0,ε]`, linear from zero to one on `[ε,2ε]`, and one after
`2ε`. The L² error and the term `(1−η_ε)u'` tend to zero. For the only
remaining product derivative term,

\[
\|\eta_\varepsilon'u\|_2^2
 \le\varepsilon^{-2}\int_0^{2\varepsilon}|u(r)|^2\,dr
 \le2\int_0^{2\varepsilon}|u'(t)|^2\,dt\longrightarrow0.
\tag{2.3}
\]

Next multiply by `χ_R`, equal to one up to R, linear to zero on `[R,2R]`,
and zero beyond `2R`. The tail terms tend to zero and
`‖χ_R'u‖₂≤R⁻¹‖u‖₂`. Products of the two cutoffs with u therefore approximate
u in H¹ and are supported in compact intervals bounded away from zero.
Extend each such product by zero to the real line and convolve with a smooth
compact approximate identity whose support radius is smaller than half its
distance from zero. The convolution is in `C_c^∞(0,∞)` and converges in H¹:
weak derivatives commute with convolution, and translation continuity in L²
gives convergence of both the function and derivative. A diagonal sequence
proves `u∈D`.

This proves the actual identity

\[
D=\{u\in H^1(0,\infty):u(0)=0\}.
\tag{2.4}
\]

No pointwise boundary condition at infinity is added. All integrations by
parts below are first performed on compact tests and then extended through
this H¹ approximation; no unproved boundary limit at infinity is used.

The foundational facts invoked in this section are Lebesgue integration,
completeness of L², translation continuity in L², and smooth convolution.
The needed weak derivative and trace deductions have been supplied explicitly.

## 3. Hardy and continuity of the singular terms

For `v∈C_c^∞(0,∞;ℂ)`, integration of the derivative of `|v|²/r` gives

\[
\int_0^\infty\frac{|v|^2}{r^2}
 =\int_0^\infty\frac{(|v|^2)'}r
 =2\operatorname{Re}\int_0^\infty\frac{\overline v\,v'}r
 \le2\|v/r\|_2\|v'\|_2.
\tag{3.1}
\]

The sign in this one-dimensional identity is positive. Dividing when the
quotient norm is nonzero, and treating zero separately, yields

\[
\|v/r\|_2\le2\|v'\|_2.
\tag{3.2}
\]

For `u∈D`, choose compact smooth `u_j→u` in H¹. Equation (3.2) on differences
makes `u_j/r` Cauchy in L². Its limit is the actual function `u/r`: on each
interval `[1/m,m]`, multiplication by `1/r` is bounded on L², so that
restriction of the limit agrees with `u/r`; these intervals cover `(0,∞)`.
Passing to the limit proves (3.2) on D.

Consequently `J(u)=∫|u|²/r` is finite, since

\[
0\le J(u)\le\|u/r\|_2\|u\|_2\le2\|u'\|_2\|u\|_2.
\tag{3.3}
\]

The maps `u↦u'`, `u↦u/r`, and `u↦u` are continuous from D with its H¹ norm
to K. Their L² pairings, including `J(u)=⟨u/r,u⟩`, are therefore continuous
in H¹. This justifies every passage from compact identities to D below.

## 4. Three first-order operators on one declared domain

Define densely defined operators from K to K, all with exactly domain D:

\[
Au=u'-\frac ur+Zu,\qquad
Bu=-u'-\frac ur+Zu,\qquad
Cu=u'-\frac{2u}r+\frac Z2u.
\tag{4.1}
\]

Their values lie in K by Hardy, and they are continuous as maps from H¹₀
to K. For example `‖Bu‖₂≤3‖u'‖₂+Z‖u‖₂`. This H¹ continuity is distinct
from the later assertion that B is closed as an unbounded operator on K.

Compact integration by parts, followed by Section 3 continuity, gives for
all `u,v∈D`

\[
\langle Au,v\rangle=\langle u,Bv\rangle.
\tag{4.2}
\]

Only this pairing identity on the declared common domain is used. There is
no assertion here that `D(A*)=D`, or that `A*=B` with an identified maximal
adjoint domain.

Writing `D₁=‖v'‖₂²`, `R=‖v/r‖₂²`, `M=‖v‖₂²`, direct compact expansion
uses

\[
2\operatorname{Re}\int\overline v\,v'=0,
\qquad
2\operatorname{Re}\int\overline v\,v'/r=R.
\tag{4.3}
\]

It yields the following exact identities, extended to every v∈D:

\[
\begin{aligned}
\|Av\|_2^2&=D_1-2ZJ(v)+Z^2M,\\
\|Bv\|_2^2&=D_1+2R-2ZJ(v)+Z^2M,\\
\|Cv\|_2^2&=D_1+2R-2ZJ(v)+\frac{Z^2}{4}M.
\end{aligned}
\tag{4.4}
\]

In particular

\[
\|Bv\|_2^2=\|Cv\|_2^2+\frac{3Z^2}{4}\|v\|_2^2,
\qquad
q_Z[v]=\frac12\|Av\|_2^2-\frac{Z^2}{2}\|v\|_2^2.
\tag{4.5}
\]

There is also a useful graph estimate, since pointwise for r>0

\[
\frac2{r^2}-\frac{2Z}r+Z^2
 =2\left(\frac1r-\frac Z2\right)^2+\frac{Z^2}2\ge0.
\]

Integrating in the B identity proves

\[
\|v'\|_2\le\|Bv\|_2,
\qquad
\|v\|_2\le\frac{2}{\sqrt3 Z}\|Bv\|_2.
\tag{4.6}
\]

Both estimates are needed in the closed-range argument. The second alone
would control the function but would not prove convergence in the prescribed
H¹₀ domain.

## 5. B is closed and its range is closed

Suppose `v_j∈D`, `v_j→v` in K and `Bv_j→w` in K. The first estimate in
(4.6) on differences shows that `v_j'` is Cauchy in K. Hence `v_j` is Cauchy
in H¹₀. Its H¹ limit lies in D by completeness and agrees with v in K.
The H¹ continuity of B gives `Bv=w`. Thus B is closed with exactly domain D.

Now suppose only that `Bv_j→w` in K. The second estimate in (4.6) makes
`v_j` Cauchy in K, and the first makes the derivatives Cauchy. The same
argument gives `v∈D` with `Bv=w`. Hence

\[
\operatorname{ran}B\text{ is a closed linear subspace of }K.
\tag{5.1}
\]

The operator B is also injective, by its strictly positive lower bound.

## 6. Identify the range by a local distributional ODE

Let `w∈(ran B)⊥`. Testing against `Bφ` for `φ∈C_c^∞(0,∞;ℂ)` gives

\[
0=\langle B\phi,w\rangle
 =\int_0^\infty
 \left(-\overline{\phi'}-\frac{\overline\phi}r+Z\overline\phi\right)w.
\]

Since conjugates of compact complex tests are again all compact complex
tests, this is exactly

\[
w'=\left(\frac1r-Z\right)w
\quad\text{in distributions on }(0,\infty).
\tag{6.1}
\]

For any `0<a<b<∞`, its right side is in L²(a,b), so w has the local
absolutely continuous representative from Section 2. The ordinary product
rule there gives

\[
\left(\frac{e^{Zr}}r w(r)\right)'=0.
\tag{6.2}
\]

This multiplier and its derivative are bounded on each such compact
interval. Thus the product is absolutely continuous there and is constant.
Taking the nested intervals `(1/m,m)`, `m≥2`, shows that the constants agree
on overlaps. Consequently `w=c g_Z` almost everywhere on the entire
half-line for a single complex c. No endpoint behavior was assumed for w;
the ODE is solved only where its coefficients are smooth and finite.

Conversely `g_Z∈D`: its function and derivative are square-integrable,
its trace at zero is zero, and Section 2 applies. Polynomial times decaying
exponential integrability follows, for example, by elementary integration
by parts of `∫₀∞ r^k e^{-a r}dr=k!/a^{k+1}` for a>0. Direct differentiation
gives `Ag_Z=0`, so (4.2) gives `⟨Bv,g_Z⟩=0` for every v∈D. Hence

\[
(\operatorname{ran}B)^\perp=\operatorname{span}_{\mathbb C}\{g_Z\}.
\tag{6.3}
\]

The elementary Hilbert-space orthogonal projection theorem gives
`(M⊥)⊥=M` for a closed linear subspace M. Apply it to the range whose
closedness was proved in Section 5, obtaining the **exact range**

\[
\operatorname{ran}B=\{g_Z\}^{\perp}.
\tag{6.4}
\]

This is stronger than density of the range. It follows without making a
claim about the full adjoint domain of A or B.

## 7. Complement inequality

Take `u∈D∩{g_Z}⊥`. The case u=0 is immediate. Otherwise (6.4) supplies a
unique `v∈D` with `u=Bv`, and (4.6) gives
`‖v‖₂≤2‖u‖₂/(√3 Z)`. Equation (4.2) and Cauchy–Schwarz yield

\[
\|u\|_2^2
 =\langle u,Bv\rangle
 =\langle Au,v\rangle
 \le |\langle Au,v\rangle|
 \le\|Au\|_2\|v\|_2
 \le\frac{2}{\sqrt3 Z}\|Au\|_2\|u\|_2.
\tag{7.1}
\]

Here the two initial inner products equal the nonnegative real number
`‖u‖₂²`; the displayed comparison with the modulus refers to that real
number. Cancelling the positive norm gives

\[
\|Au\|_2^2\ge\frac{3Z^2}{4}\|u\|_2^2.
\tag{7.2}
\]

Substitution in the exact A identity (4.5) proves Theorem R:

\[
q_Z[u]\ge\frac12\left(\frac34-1\right)Z^2\|u\|_2^2
 =-\frac{Z^2}{8}\|u\|_2^2.
\]

## 8. Sharpness and equality

Set `v₂(r)=r²e^{-Zr/2}`. Both v₂ and u₂ from (1.3) belong to D by
the same polynomial-exponential and trace check as g_Z. Direct differentiation
gives

\[
Cv_2=0,\qquad Bv_2=-3u_{2,Z},\qquad
Au_{2,Z}=-\frac{Z^2}{4}v_2.
\tag{8.1}
\]

Since u₂ is in ran B, it is orthogonal to g_Z. Equations (4.5) and (8.1)
give

\[
9\|u_{2,Z}\|_2^2=\frac{3Z^2}{4}\|v_2\|_2^2,
\qquad
\|Au_{2,Z}\|_2^2=\frac{Z^4}{16}\|v_2\|_2^2
 =\frac{3Z^2}{4}\|u_{2,Z}\|_2^2.
\tag{8.2}
\]

This nonzero u₂ realizes equality in (1.2), proving sharpness.

Conversely suppose a nonzero u realizes equality in (1.2). Equation (4.5)
then forces `‖Au‖₂=(√3 Z/2)‖u‖₂`. For its range preimage v, (7.1) and
the bound on ‖v‖ force `‖Bv‖₂²=(3Z²/4)‖v‖₂²`. Thus `Cv=0` by (4.5).
Solving this local ODE as in Section 6 gives `v=c r²e^{-Zr/2}`. Hence
`u=Bv=−3c u₂`. Zero also lies in this span, completing the equality
characterization. No classification of higher radial levels is needed.

## 9. Rank-one form comparison

For arbitrary u∈D, put `α=⟨ĝ_Z,u⟩` and `w=u−αĝ_Z`. Then w∈D,
`⟨ĝ_Z,w⟩=0`, and `‖u‖₂²=|α|²+‖w‖₂²`. Because `Aĝ_Z=0`, the A-square
identity gives

\[
q_Z[u]=q_Z[w]-\frac{Z^2}{2}|\alpha|^2.
\]

Applying Theorem R to w proves (1.4). If an unnormalized coefficient is
preferred, `‖g_Z‖₂²=1/(4Z³)` by the elementary radial integral, and
`|⟨ĝ_Z,u⟩|²=|⟨g_Z,u⟩|²/‖g_Z‖₂²`.

## 10. Adversarial checks, literature comparison, and formal frontier

The attempted domain failure was that a positive lower bound on B might
leave its range merely dense in the complement. Equations (4.6) control
both the function and derivative and establish closedness in the exact
H¹₀ domain, repairing that potential gap. The ODE argument is performed on
compact subintervals and then glued; it never differentiates an unbounded
integrating factor globally. Compact approximation handles all endpoint
terms. Complex pairing conventions and the sign in the one-dimensional
Hardy identity were checked explicitly. Cancellation in (7.1) occurs only
after treating u=0.

The independent reviewer `hardy_foundations` inspected the proposed domain,
range, complex pairing, and kernel arguments before this file was finalized
and found no defect. A subsequent review of this exact file should be bound
to its final hash in a separate review record. Agreement is supplemental
evidence, not a substitute for the proof.

Primary comparison: the [author-hosted Teschl text, §10.4](https://www.mat.univie.ac.at/~gerald/ftp/book-schroe/schroe.pdf)
was accessed. Theorem 10.9 gives hydrogen levels; equations (10.68)–(10.73)
and Theorem 10.10 present radial first-order factorizations with declared
adjoint domains. Its normalization is `−Δ−γ/r`: setting `γ=2Z` and dividing
energies by two yields `−Z²/2` and `−Z²/8`. This confirms applicability and
classical precedent. The proof above supplies the needed complement form
bound directly and does not import that book’s adjoint-domain or complete
spectral-classification claims. No novelty is asserted.

No Lean theorem for Theorem R is claimed in this file. Its next exact formal
interfaces are: half-line H¹₀ density and Hardy; the three square identities;
closed range on the declared domain; distributional ODE kernel; and the
orthogonal-complement pairing argument. The parent workstream separately
owns angular Poincaré and the actual three-dimensional assembly. Merely
adding Theorem R as an assumed field would not discharge those obligations.
