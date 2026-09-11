> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Independent derivation of correlated-Gaussian Coulomb moments

Status: human-readable mathematical derivation supplemented by bounded independent arithmetic checks. This file does not assert a Lean proof or itself establish a completed H₂ certificate. All formulas concern the full Gaussian integrals on ℝ⁶, with no spatial cutoff. The implementation under audit is owned separately.

## Convention and normalization

Write x=(x₁,x₂), where xᵢ∈ℝ³, and let A be a real symmetric positive-definite 2×2 matrix. The normalized density is

\[
 p_A(x)=Z_A^{-1}\exp[-(x-\mu)^T(A\otimes I_3)(x-\mu)],
 \qquad Z_A=\pi^3(\det A)^{-3/2}.
\]

Thus Cov(x)=(A⁻¹⊗I₃)/2. The factor 1/2 belongs to the covariance, not the definitions a,b,c below. An unnormalized integral is its expectation times Z_A. A product of two shifted Gaussians additionally carries the usual completed-square scalar prefactor.

For nonzero v,w∈ℝ², define the three-vectors

\[
Y=v^Tx-R,\quad W=w^Tx-S,\quad
m=v^T\mu-R,\quad n=w^T\mu-S
\]

and scalars

\[
a=v^TA^{-1}v>0,\quad b=w^TA^{-1}w>0,\quad
c=v^TA^{-1}w,\quad
T=|m|^2/a,\quad U=|n|^2/b,\quad C=c(m\cdot n)/(ab).
\]

The H₂ axial specialization replaces m,n by their signed axial components. The formulas through the independent-form case do not require axial means.

## Independent linear forms: compact integrals in two and one dimensions

Suppose v,w are linearly independent. Then δ=1−c²/(ab)>0. Put r=c²/(ab). The exact expectation is

\[
\boxed{\quad
\mathbb E\frac1{|Y||W|}
=\frac4{\pi\sqrt{ab}}\int_0^1\int_0^1
 \frac{\exp[-N(u,z)/D(u,z)]}{D(u,z)^{3/2}}\,du\,dz,\quad}
\]

where

\[
D=1-r u^2z^2,\qquad
N=T u^2+U z^2-2C u^2z^2.
\]

On the real square D≥δ and N≥0. The latter also follows directly from the nonnegative quadratic form in the Gaussian integration below. The integrand is smooth up to every boundary.

Proof: for a positive radius,

\[
\frac1q=\frac2{\sqrt\pi}\int_0^\infty e^{-t^2q^2}\,dt.
\]

Tonelli applies to the two nonnegative integrals. Completing the Gaussian square gives

\[
\mathbb E[e^{-t^2|Y|^2-s^2|W|^2}]
=\Delta^{-3/2}
\exp\!\left[
-\frac{t^2|m|^2+s^2|n|^2+
t^2s^2(b|m|^2+a|n|^2-2c\,m\cdot n)}{\Delta}\right],
\]

with

\[
\Delta=1+at^2+bs^2+(ab-c^2)t^2s^2.
\]

Substitute t=u/[√a√(1−u²)] and s=z/[√b√(1−z²)]. The two Jacobians cancel the factors (1−u²)³ᐟ²(1−z²)³ᐟ² in Δ⁻³ᐟ². The numerator simplifies to N and the denominator to D. Limits at the measure-zero endpoints are taken continuously. Finiteness also follows by Cauchy–Schwarz from the finite individual inverse-square expectations derived below.

There is a stronger reduction to a single compact integral in the axial case. Set

\[
L(z)=1-rz^2,\qquad B(z)=\frac{(m-cn z^2/b)^2}{a}.
\]

Then

\[
\boxed{\quad
\mathbb E\frac1{|Y||W|}
=\frac4{\pi\sqrt{ab}}\int_0^1
\frac{e^{-Uz^2}}{\sqrt{L(z)}}\,
F_0\!\left(\frac{B(z)}{L(z)}\right)\,dz.\quad}
\]

To prove this, the exact numerator identity is

\[
\frac{N(u,z)}{D(u,z)}
=Uz^2+\frac{B(z)u^2}{1-rz^2u^2}.
\]

At fixed z substitute v=u/√(1−rz²u²). Its derivative is D⁻³ᐟ², so the remaining u integral becomes the Gaussian integral from v=0 to v=1/√L. Scaling this interval to [0,1] gives F₀(B/L)/√L. The condition δ>0 makes every step smooth at z=1. This reduction was proposed independently by the residual-design agent and checked here.

The one-dimensional integrand is the u integral of the earlier two-dimensional integrand. Any uniform complex-disc bound on that earlier integrand with u∈[0,1] real therefore also bounds the one-dimensional function and its Cauchy derivatives: integration has length one. This permits certified one-dimensional Gauss or Taylor quadrature without a new unproved special-function derivative estimate.

Two useful independent checks are:

* If c=0, the answer factors as 4F₀(T)F₀(U)/(π√ab), where F₀(q)=∫₀¹exp(−qt²)dt.
* If m=n=0, the answer is 4arcsin(√r)/(π√ab√r), with its continuous r=0 value. Integrating first in u proves this identity directly. In particular a=b=1,c=1/2 gives exactly 4/3.

## Proportional forms: equal centers

Reduce w=kv, k≠0, by extracting 1/|k| and replacing S by S/k. It remains to treat a single three-dimensional Gaussian Y with density (πa)⁻³ᐟ²exp(−|y−m|²/a).

For the same center R, writing T=|m−R|²/a gives

\[
\boxed{\quad
\mathbb E\,|Y-R|^{-2}
=\frac2a\int_0^1 \exp[-T(1-z^2)]\,dz.\quad}
\]

Indeed, 1/q²=∫₀∞exp(−τq²)dτ. Gaussian integration gives (1+aτ)⁻³ᐟ²exp[−τ|m−R|²/(1+aτ)]. The substitution z=(1+aτ)⁻¹ᐟ² proves the result. It is finite for every a>0 and every displacement. At m=R it equals 2/a exactly.

## Proportional forms: distinct axial centers, a smooth one-dimensional integral

Assume R≠S and m,R,S are collinear. Let e=(S−R)/|S−R|, let c₀=(R+S)/2, and put d=|S−R|/2>0 and m=c₀+z e, where z is signed. Then

\[
\boxed{\quad
\mathbb E\frac1{|Y-R||Y-S|}
=\frac1a\int_{-1}^{1}
\exp\!\left[\frac{d^2-z^2}{a}(1-t^2)\right]
\operatorname{erfc}\!\left(\frac{d-zt}{\sqrt a}\right)\,dt.\quad}
\]

This is an entire, smooth integrand in t. It avoids the corner singularity obtained by inserting r=1 into the two-dimensional independent-form formula.

Proof: use prolate spheroidal coordinates ξ≥1, t∈[−1,1], φ∈[0,2π). The distances are d(ξ+t), d(ξ−t), and the volume element is d³(ξ²−t²)dξ dt dφ. Consequently the volume divided by the product of distances is d dξ dt dφ. The Gaussian squared displacement is

\[
|y-m|^2=d^2(\xi^2+t^2-1)-2dz\xi t+z^2.
\]

Complete the square in ξ and evaluate its integral from 1 to infinity. Its factor √(πa)/(2d) multiplies the angular factor 2πd and the Gaussian normalization (πa)⁻³ᐟ² to give exactly 1/a. The remaining exponent and erfc argument are those displayed.

The same formula extends continuously to d=0. Pairing t and −t uses erfc(q)+erfc(−q)=2 and recovers the inverse-square formula above. For z=0, another exact check is

\[
\mathbb E\frac1{|Y-R||Y-S|}
=\frac2a e^{d^2/a}\operatorname{erfc}(d/\sqrt a)\,F_0(d^2/a).
\]

### Explicit rational derivative bounds for the one-dimensional formula

Write

\[
A_0=(d^2-z^2)/a,\quad D_0=d^2/a,\quad E_0=dz/a,\quad
k=2z/\sqrt{\pi a},
\]

and denote the displayed integrand by f(t). Set g(t)=exp[−(dt−z)²/a]. Exact differentiation and cancellation of exponents yield

\[
f'=-2A_0tf+kg,\qquad g'=-2(D_0t-E_0)g.
\]

Define rational polynomials recursively:

\[
P_0=1,\ H_0=0,\quad
P_{n+1}=P_n'-2A_0tP_n,\quad
H_{n+1}=P_n+H_n'-2(D_0t-E_0)H_n.
\]

Then f⁽ⁿ⁾=Pₙf+kHₙg, by induction. On [−1,1], 0≤g≤1. Also f≤1 if |z|≤d: its erfc argument is nonnegative, and erfc(q)≤exp(−q²) for q≥0 gives f≤g≤1. The erfc bound follows by differentiating exp(−q²)−erfc(q), whose derivative changes sign only once and whose endpoint values are zero. If |z|>d, the exponential prefactor is at most one and erfc≤2, so f≤2.

If ||P||₁ is the sum of absolute polynomial coefficients, and F is 1 or 2 as just specified, the explicit bound

\[
\sup_{[-1,1]}|f^{(n)}|
\le M_n:=F\|P_n\|_1+|k|_{\rm upper}\|H_n\|_1
\]

uses only rational recurrences and a certified rational upper bound on |k|. On a partition into cells of half-width at most h, integrate the degree-p Taylor polynomial at each rational cell midpoint. The total expectation remainder is at most

\[
\frac{2M_{p+1}h^{p+1}}{a(p+1)!}.
\]

All polynomial integrals are rational. The values of f and g at midpoints are enclosed using rational outward square roots, exponentials, π and erfc. One option is erfc(q)=1−2qF₀(q²)/√π; large positive arguments can lose enclosure accuracy through cancellation, so the working precision must be increased or a separate erfc-tail enclosure used. This is an explicit numerical issue, not an omitted error term.

A sharper expression exploits cancellation of the odd Taylor powers. For K equal cells, tᵢ=−1+(2i+1)/K, and p≥1,

\[
Q_{K,p}=\frac1a\sum_{i=0}^{K-1}\sum_{j=0}^{p-1}
\frac{2f^{(2j)}(t_i)}{(2j+1)!\,K^{2j+1}},
\qquad
|I-Q_{K,p}|
\le\frac{2M_{2p}}{a(2p+1)!\,K^{2p}}.
\]

Integrate the degree-(2p−1) Taylor polynomial and its pointwise remainder |s|²ᵖM₂ₚ/(2p)! on each cell to obtain this bound. Every node is rational; algebraic Gaussian quadrature nodes are unnecessary.

## Polynomial factors from the kinetic energy

For any polynomial P, a single Coulomb factor admits

\[
\mathbb E\frac{P(x)}{|v^Tx-R|}
=\frac2{\sqrt{\pi a}}\int_0^1e^{-Tu^2}\,
\mathbb E_u[P(x)]\,du,
\]

where the tilted Gaussian has

\[
\mu(u)=\mu-\frac{u^2}{a}(A^{-1}v)m,\qquad
\Sigma(u)=\frac12\left[A^{-1}
-\frac{u^2}{a}(A^{-1}v)(A^{-1}v)^T\right]\otimes I_3.
\]

This follows from the same completed square before the one-parameter substitution. The limiting covariance at u=1 is allowed to be semidefinite; its polynomial moments are continuous there. The mean is affine in u² and the covariance is affine in u². A degree-two P therefore has a tilted expectation of degree at most two in u², requiring only F₀(T),F₁(T),F₂(T), with Fⱼ(T)=∫₀¹u²ʲexp(−Tu²)du.

For reference, with mean mᵢ and covariance Σᵢⱼ, the raw moments are

\[
\mathbb E X_iX_j=m_im_j+\Sigma_{ij},
\]

\[
\mathbb E X_iX_jX_kX_l
=m_im_jm_km_l+
\sum_{\text{six pairs }ab}\Sigma_{ab}m_cm_d+
\Sigma_{ij}\Sigma_{kl}+\Sigma_{ik}\Sigma_{jl}+\Sigma_{il}\Sigma_{jk}.
\]

These identities follow by differentiating the finite Gaussian generating function exp(t·m+tᵀΣt/2) at zero. Thus the polynomial kinetic×kinetic term needs only explicit moments through degree four; kinetic×potential terms need degree-two single-Coulomb moments; potential×potential terms need only the scalar two-Coulomb integrals. No polynomial two-Coulomb quadrature is necessary for the strong residual of a Gaussian trial.

For an efficient matrix form, let the individual primitives have Aᵢ,pᵢ, set Bᵢ=Aᵢ², and write

\[
K_i(x)=(-\tfrac12\Delta g_i)/g_i
=3\operatorname{tr}(A_i)-2Q_i(x),\quad
Q_i(x)=\sum_{\ell=1}^3(x_\ell-p_{i,\ell})^TB_i(x_\ell-p_{i,\ell}).
\]

For a pair density with per-coordinate covariance S=(Aᵢ+Aⱼ)⁻¹/2 and axial dᵢ=μ−pᵢ,

\[
\mathbb E Q_i=3\operatorname{tr}(B_iS)+d_i^TB_id_i,
\]

\[
\mathbb E[K_iK_j]
=\mathbb E[K_i]\mathbb E[K_j]
+24\operatorname{tr}(B_iSB_jS)
+16d_i^TB_iSB_jd_j.
\]

To prove the second identity, center the Gaussian and use its vanishing odd moments and the fourth-moment formula above. Each of the three independent Cartesian directions contributes 2tr(BᵢSBⱼS) to Cov(Qᵢ,Qⱼ), and only the axial mean contributes the linear-term covariance 4dᵢᵀBᵢSBⱼdⱼ. Multiplication by four from Kᵢ,Kⱼ gives the displayed constants.

Every positive-definite Gaussian primitive is Schwartz and belongs to H²(ℝ⁶). Multiplication by each Coulomb inverse leaves it in L² because the inverse is square integrable locally in three transverse dimensions. Thus Hψ is well defined for a finite Gaussian sum, and its squared norm is the strong second spectral moment. This uses D(H), not membership in the domain of the composed operator H².

## An explicit convergent quadrature for independent forms

This gives a rigorous fallback and derivative bounds; it is not a claim that the most conservative uniform partition is fast for many basis functions.

Let f=D⁻³ᐟ²exp(−N/D) be the compact-square integrand and δ=1−r>0. At any real center (u₀,z₀)∈[0,1]², consider a complex polydisc with both radii ρ=δ/32. On this polydisc, |u|,|z|≤2 and

\[
|u^2z^2-u_0^2z_0^2|\le15\rho<\delta/2.
\]

Hence Re D≥δ/2, so its inverse power has an analytic branch. Put Q=4(T+U)+32|C|. Then |N|≤Q, and a completely rational modulus bound is

\[
|f|\le M:=(2/\delta)^2\,4^{\lceil 2Q/\delta\rceil}.
\]

Here |D|⁻³ᐟ²≤(2/δ)² and exp(q)≤4^{ceil(q)} for q≥0. Cauchy's integral formula supplies the explicit derivative bounds

\[
|\partial_u^i\partial_z^j f(u_0,z_0)|
\le i!j!\,M\,\rho^{-i-j}.
\]

Choose a rational partition with cell half-width h≤ρ/4. The tensor Taylor polynomial retaining powers 0≤i,j≤p has pointwise remainder at most

\[
\frac{2M(h/\rho)^{p+1}}{(1-h/\rho)^2}
\le M4^{-p}.
\]

The same bound applies to its integral over the unit square. Multiply it by 4/(π√ab), enclosed outward, for the expectation error. Derivatives at rational centers are rational multiples of D₀⁻³ᐟ²exp(−N₀/D₀); their truncated coefficients can be obtained by formal polynomial multiplication, reciprocal, binomial series and exponential series. Every integrated monomial is rational, so interval roundoff is separately enclosed.

This proves termination for fixed rational input with δ>0: the cell count is finite and p can be increased until the displayed bound meets the requested tolerance. The resulting constants depend explicitly on δ,T,U,C and the normalization scale. It does not establish a bound uniform in basis size, exponent range or molecular geometry.

A practical implementation may use larger, adaptively certified polydiscs. For radii Rᵤ,R_z set Bᵤ=|u₀|+Rᵤ, B_z=|z₀|+R_z and eᵤ=2|u₀|Rᵤ+Rᵤ², e_z=2|z₀|R_z+R_z². Then

\[
\Delta_D=r(e_uB_z^2+u_0^2e_z),\qquad
\Delta_N=Te_u+Ue_z+2|C|(e_uB_z^2+u_0^2e_z).
\]

If Δ_D<D₀, the local real exponent q=N₀/D₀≥0 obeys

\[
\left|\frac ND-q\right|
\le\frac{\Delta_N+q\Delta_D}{D_0-\Delta_D}.
\]

These rational bounds can substantially reduce both the exponential modulus bound and the number of cells while retaining the same Cauchy/Taylor remainder proof.

## Boundaries of this audit

The proportional distinct-center one-dimensional reduction explicitly assumes axial collinearity. For that case, a Gaussian mean off the common axis requires a different reduction, such as the general two-parameter Gaussian integral or an additional angular integration. The independent-form formula assumes δ>0; inserting δ=0 into its smoothness or derivative estimates is invalid. All rigorous quadrature error budgets must include interval evaluation error as well as Taylor truncation. Trial coefficient cancellation can demand more internal precision than the final energy interval width suggests.

## Independent checker review

The checker contracts canonical primitive-pair contributions with signed rational coefficients. For the group of simultaneous inversion and electron interchange, unitarity and commutation with the Hamiltonian give

\[
\langle\phi_i,O\phi_j\rangle
=4\sum_{U\in G}\langle g_i,OUg_j\rangle.
\]

For the second moment, replace the operator notation by the bilinear form ⟨Hgᵢ,Hgⱼ⟩. Interchange of a real primitive pair and joint application of a symmetry preserve all three moments. Thus collecting their signed coefficients before evaluation is valid. The common omitted factor is 4π³ in the norm, energy numerator and squared-action numerator.

Suppose the distinct collected contributions have nonzero weights wⱼ and positive primitive overlaps sⱼ. The Gram prepass gives an outward trial norm interval with lower endpoint S₋>0. Choose any strictly positive rational allocation weights qⱼ and assign each double-Coulomb kernel the desired width

\[
\varepsilon_j=\frac{\eta S_-q_j}
 {25(\sum_kq_k)|w_j|(s_j)_+}.
\]

There are five unit-magnitude potential charges, so the five diagonal and ten doubled cross terms have total absolute coefficient 5+2·10=25. If every kernel meets its assigned width, the portion of the contracted second-moment width caused by those kernel uncertainties is at most

\[
\sum_j25|w_j|(s_j)_+\varepsilon_j=\eta S_-.
\]

Division by a norm at least S₋ makes that contribution at most η. This is a budget for this source of error only. Overlap uncertainty, other interval arithmetic, variation of the norm denominator, and kernels that reach a resource cap still contribute to the full output width. The checker retains all actual interval widths, so the budget is not substituted for an achieved bound.

Uniform allocation is qⱼ=1. A rational upper enclosure of √(|wⱼ|(sⱼ)₊) is another admissible choice. Only positivity and exact normalization by the same sum of qⱼ are required for the budget proof; the square-root choice is an efficiency heuristic and does not itself prove a runtime bound.

For the computed mean interval [m₋,m₊] and variance upper bound v₊, the check m₊<β guarantees positive β−m₊. If the exact mean and variance are m,v, then

\[
m-\frac{v}{\beta-m}
\ge m_- -\frac{v_+}{\beta-m_+}.
\]

This follows separately from m≥m₋, v≤v₊ and β−m≥β−m₊; it does not assume monotonicity of the whole Temple expression as a function of m. Taking the maximum with an independently established lower bound is valid. The final decimal lower endpoint is rounded downward and the upper endpoint upward by integer division.

The final source and trial hashes bind the recorded data to file bytes. Cache keys include rational primitive parameters, R, precision, requested tolerance, quadrature settings, source hashes and the weighted tolerance when used. A cache record itself is a trusted reproducibility artifact: reading it does not re-prove its stored moments. A final run with no reused entries avoids that additional dependency. The source files must remain frozen during a run so hashes of files on disk describe the code actually loaded.

The independent executable checks the Gaussian algebra by Cartesian polynomial differentiation and a raw-moment recurrence, and checks kernels against exact special values, independent series and the original uneliminated integral. It additionally exercises the checker on temporary **synthetic** moments: a direct 16-image signed Gram expansion, weighted allocation, source-dependent cache keys, cache fresh/reuse behavior, exact input rejection and Temple endpoint arithmetic. Those temporary records are deleted and are not molecular certificates. Optional replay of a completed molecular certificate checks its stored final scalars and hashes without independently rebuilding its large continuum moment contraction.

These are finite exact arithmetic checks supporting the paper proofs. They are not universal theorems checked in Lean and do not turn the Python execution or the continuum integral identities into a formal proof.
