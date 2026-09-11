> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Independent audit of exterior distance analyticity

Audited on 2026-09-09: `EXTERIOR_ANALYTIC_ATTEMPT.md`, with the established uniform KS operator lemma and quantitative descent in `UNIFORM_ANALYTIC_AUDIT.md` and `RWA_THEOREM.md`. This is a paper audit. No numerical experiment or Lean verification was performed.

**Verdict: PASS**, with one minor lower-bound bookkeeping correction recorded below. The argument gives a holomorphic distance/perimetric radius c/(1+S) and a common holomorphic amplitude bound for the actual wavefunction throughout S>=D. Its assumptions are supplied by the existing physical ground-state and uniform analytic results. This audit does not prove the later global dictionary approximation.

## 1. Global Moser bound: constants checked

The Lipschitz phase F=-Z(r+s)+u/2 obeys |grad F|<=L=sqrt(2)(Z+1/2), and distributionally Delta F=2V. Conjugation cancels the singular potential and gives (E3) with bounded measurable drift and zeroth-order terms. It does not differentiate those coefficients. The local multiplier is bounded above and below, and maps the physical H¹ function to H¹; the product identity can be justified distributionally using the local H² phase and sliced Hardy bounds. Positivity licenses the power iteration after truncation.

For the quantities X,Y,T used in the proof, let a_p=4(p-1)/p². Absorbing a_p X²/4 from each cross term gives

\[
X^2\le\frac{2p^2}{(p-1)^2}Y^2
+\frac{p^2 B^2}{2(p-1)^2}T^2
+\frac{p^2 C_0}{2(p-1)}T^2.
\]

For p>=2 these coefficients are bounded by 8, 2B², pC_0, respectively. This proves the first line of (E4); the second follows by bounding grad(eta w) by its two summands. No hidden dependence on the ball center enters.

The six-dimensional W^(1,1) inequality applied to |g|^(5/2) gives ||g||_3<=(5/2)||grad g||_2, so the sufficient constant 3 is valid. The iteration product is exactly bounded by

\[
(72K_Z)^{3/2}6^3<2^{18}K_Z^{3/2},
\]

because sum_j 1/p_j=3/2 and sum_j j/p_j=3. The initial L² factor is at most exp(2L); returning to psi on the unit ball costs exp(L). Therefore the displayed bound

\[
\|\psi_Z\|_\infty\le2^{18}K_Z^{3/2}e^{3L}
\]

checks with the stated K_Z. It uses neither an invalid H²(R^6)-to-L-infinity embedding nor analyticity of the conjugated drift.

## 2. Translated Cartesian and KS charts

For x_1=hX and x_2=t_0+ht, multiplying the scaled physical equation by 8h²|y|² after X=K(y) gives exactly (E6). In particular, its nuclear constant is -8hZ, spectator terms carry 8h²|y|², and the energy term is -8h²E_Z|y|². The principal operator is the fixed -Delta_y-4|y|²Delta_t.

On the fixed normalized cylinder, a complex perturbation of a real spectator vector v by less than |v|/4 changes v dot v by less than (9/16)|v|². Its square root and reciprocal therefore have common holomorphic bounds whenever |v| is bounded below. This verifies a uniform analytic norm for B_h/h, independent of the translated center t_0, including |t_0| tending to infinity. Taking h small once meets the absorption condition in (U5)–(U6). The lifted L² norm is uniformly bounded by the Moser amplitude and the fixed cylinder volume; no singular pullback Jacobian is being estimated by an unjustified norm equivalence.

The existing operator lemma then supplies common factorial bounds. Quantitative KS descent produces analytic coefficients with common physical radii and sup norms; the second coefficient costs only the fixed factor h^(-1). Electron–electron coordinates have fixed linear scaling and principal operator -Delta_y-|y|²Delta_t, so the same argument applies. The distributional KS transformation is the same isolated-pair transformation verified in the prior proof, with all spectator terms analytic on the chosen chart.

On the complement of smaller pair tubes, r,s,u have a fixed positive lower bound. Fixed-radius Cartesian balls therefore have uniform analytic potential bounds. The existing constant-principal-part estimate and factorial induction apply with common constants. If these balls are rescaled to unit size, their L² bound picks up a fixed factor h_*^(-3); this depends only on Z,D and has no effect on exterior uniformity. Alternatively the estimate can be kept on the fixed physical balls, where the L² input is at most one.

## 3. Minor chart-center bookkeeping correction

A near-electron-pair exterior point can project to an axis point with |t_0| slightly less than D/2. For example, r=s=D/2 and 0<u small gives

\[
|(x_1+x_2)/2|=\sqrt{D^2/4-u^2/4}<D/2.
\]

Thus the assertion |t_0|>=D/2 is exact on the exterior pair axis, but should not be silently reused for every projected center of a near-axis exterior point.

**Direct repair:** use D/4 for the spectator/center lower bound in the electron–electron tube charts and their distance-coordinate descent. Indeed u<4eta<=D/25 and S>=D imply r,s>12D/25, and

\[
|(x_1+x_2)/2|\ge r-u/2>11D/25>D/4.
\]

All subsequent fixed-radius and reciprocal bounds remain valid with that smaller constant. The theorem and every polynomial exponent are unchanged. This correction was sent to the author and root; it is an explicit constant adjustment, not a new regularity hypothesis.

## 4. Pair-axis descent and collinear conversion

Uniqueness of the analytic-plus-distance decomposition transfers SO(2) invariance to the analytic coefficients. The invariant series has coefficients controlled geometrically in (w,z,s-s_0), with w=x²+y²; the quantitative conversion was already audited in the prior RWA proof. At nuclear axes, (s-u)(s+u)/(2s) stays O(delta) uniformly for arbitrarily large s_0, because the apparently large factor cancels against the denominator. At electron-pair axes, the analogous t_* and z formulas have the same uniform property using the corrected D/4 separation. Thus the fixed pair-axis analytic radius does not deteriorate at infinity.

Outside pair tubes, select the larger distance as spectator at each center, so s>=S/2 and u<=S. For distance changes bounded by delta<=S/8,

\[
|\Delta(r^2+s^2-u^2)|\le(35/8)S\delta,
\qquad |s+\Delta s|\ge3S/8.
\]

Subtracting the expression for z gives |Delta z|<=8.5 delta<9 delta. Consequently

\[
|\Delta w|\le20S\delta+82\delta^2
\le102(1+S)\delta,
\]

as claimed. These estimates hold for complex changes; their proof uses absolute values, not a real ordering of the perturbed quantities.

For w<h_*²/256, the collinear projection changes the physical configuration by less than h_*/16. Choosing h_* below the fixed pair-separation margin keeps that projection collision-free. Its invariant-series domain has a fixed w-radius proportional to h_*². Taking c_0<=h_*²/2^20 makes the complex w change smaller than 102h_*²/2^20, comfortably inside the retained domain.

For w>=h_*²/256, the same bound is less than w/4. The positive square root extends holomorphically and

\[
|\Delta\sqrt w|\le32|\Delta w|/h_*
\le(3264/2^{20})h_*<h_*/16.
\]

The z and s changes are smaller still. Thus the perturbed representative lies in a uniformly controlled Cartesian chart. No derivative of a pointwise label-selection rule is taken, and the final factor two for half-perimetric variables is correct.

The overlap compatibility assertion is valid: the analytic germs coincide on the physical real interior and hence on overlaps by uniqueness. This is an analytic continuation of the same wavefunction, not an arbitrary boundary condition on the octant faces.

## 5. Exterior shell and Gevrey constants

Scaling x=tau y divides the physical analytic radius by tau. On the fixed shell S(y)<=2 this gives

\[
\frac{c}{\tau(1+2\tau)}\ge\frac{c/2}{(1+\tau)^2}.
\]

The amplitude remains bounded by the common holomorphic constant; it is not multiplied by an exponential in tau.

The grid cover has O(r_tau^(-3)) boxes, but a uniformly bounded overlap count. This distinction is load-bearing and is handled correctly. At any point only a fixed number of cutoff factors can have nonzero derivatives; compactly supported flat cutoffs have all derivatives zero at their support boundary. Consequently the telescoping partition does not introduce a factor depending exponentially on the total number of boxes. Its Gevrey constants scale as (C/r_tau)^k(k!)², with a uniformly bounded zeroth-order amplitude.

The Fourier integration-by-parts choice gives b_tau proportional to sqrt(r_tau), hence b_tau>=c/(1+tau). There are O(N²) frequency triples at largest frequency N; two Chebyshev derivatives cost at most O(N^4). The remaining coefficient tail is therefore bounded by

\[
\sum_{N>d}(N+1)^6e^{-b\sqrt N}
\le Cb^{-14}e^{-b\sqrt d/2},\qquad 0<b\le1.
\]

The exponent fourteen is correct: substituting t=sqrt(N) leaves an integrand proportional to t^13 exp(-bt/2). A uniform constant covers the finitely many small frequencies. With degree q and d=floor(q/3), this verifies the polynomial prefactor (1+tau)^14 and the exponent sqrt(q)/(1+tau) in (E12). The bounded-cube and outside-polynomial growth estimates inherit at most the same conservative prefactor.

## Audit boundary

The exterior holomorphic-radius theorem and (E12) pass after the harmless D/4 center-bound clarification. Constants are uniform over the unbounded exterior because the physical chart sizes, spectator separation, analytic model estimates, and amplitude are uniform; no unbounded-set compactness argument is used. Their numerical optimization or computability is not claimed here.

This supplies an exterior analytic input. It does not prove that the prescribed dictionary simultaneously approximates every shell or that the exterior tail of one assembled witness is small. Those are separate mathematical claims and require their own audit.
