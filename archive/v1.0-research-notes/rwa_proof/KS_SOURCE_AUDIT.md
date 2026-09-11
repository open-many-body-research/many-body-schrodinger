> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# KS and analytic-hypoellipticity primary-source audit

Status: PROVEN paper results and a quantitative rescaling route. No Lean claims. This is the bounded KS branch of the RWA audit; it is not a replacement for the main proof.

## Verified sources

**Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Sørensen (2005).** [arXiv:math-ph/0312060](https://arxiv.org/pdf/math-ph/0312060), DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6). Theorem 1.1, equations (1.8)–(1.12), applies to local distributional solutions of fixed-nucleus Coulomb equations in \(\mathbb R^{3N}\). Its explicit cusp/logarithmic factor leaves a locally \(C^{1,1}\) function, including simultaneous collisions. Theorem 1.4 and Remark 1.5, equation (1.20), give uniform-in-center \(C^{1,1}\) bounds on nested balls of fixed radii; the constant depends on the radii and Hamiltonian. These are finite-order assertions. They verify the prior extraction and local Lipschitz control, not all-order RWA. No uniform radius-scaled factorial assertion is stated there.

**Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Sørensen (2009).** [arXiv:0806.1004](https://arxiv.org/html/0806.1004), DOI [10.1007/s00220-008-0664-5](https://doi.org/10.1007/s00220-008-0664-5). Theorem 1.4 assumes a \(W^{1,2}\) distributional Coulomb eigenfunction on an open subset of \(\mathbb R^{3N}\). It proves the analytic-plus-distance decomposition at isolated pair collisions, excluding simultaneous collisions. Section 2.2, equations (2.13)–(2.17), lifts a pair chart to \(\mathbb R^4\times\mathbb R^{3N-3}\), invoking Grušin Theorem 5.1. Lemma 4.3 and Proposition 4.4 give quantitative descent from lifted Taylor coefficient bounds: if coefficients are bounded by \(C_2M_2^{|\beta|+|\gamma|}\), the displayed physical radii are \(1/(4M_2^2)\) and \(1/(2M_2)\). Constants are not asserted uniform as another collision approaches. This discharges descent once a common lifted analytic bound is supplied; qualitative Theorem 1.4 alone does not discharge RWA.

**Grušin (1971).** [Primary English paper](https://www.mathnet.ru/php/getFT.phtml?jrnid=sm&paperid=3054&what=fullteng), DOI [10.1070/SM1971v013n02ABEH001033](https://doi.org/10.1070/SM1971v013n02ABEH001033). Theorem 5.1 is an interior analytic-hypoellipticity theorem for the quasihomogeneous class defined in (0.1), (0.2), (5.1). Conditions 1 and 2 require frozen ellipticity off the degeneracy stratum and no Schwartz kernel for the transverse frozen operator at unit tangential frequency. Proposition 5.1, equations (5.20)–(5.24), proves factorial derivatives using the compact-support estimate (5.5), analytic coefficient/source bounds (5.14), and finitely many initial derivative norms. Lemmas 5.1–5.3 track commutators on shrinking bicylinders. There is no physical boundary: the degeneracy is an interior submanifold. Uniformity follows from uniform bounds on those inputs, not from Theorem 5.1's qualitative wording.

The downloaded English PDF has 31 pages; printed pp. 155–156 and 179–183 were visually inspected, including the formulas lost by web OCR. Local file: \`sources/grushin1971.pdf\`. SHA-256:
\`c5901af60d30b3a41a7e4a62576cfd1689bcd11ce7097c84299c3077534da93e\`.
The web PDF has an extra portal cover page. The PDF screenshot service failed; local Poppler rendering resolved the missing formulas.

## Exact specialization of Grušin's hypotheses

The following is our specialization, not an assertion that the original paper already treats the physical remainder.

Write the blown-up Cartesian coordinates as \((X,z)\in\mathbb R^3\times\mathbb R^3\), near \(X=0\), with \(z\) in a fixed compact set separated from zero. Let \(X=K(y)\), \(y\in\mathbb R^4\), be the KS transform. The physical rescaling \(x=\varepsilon X\) turns the eigenfunction equation into
\[
[-\Delta+2\varepsilon V-2\varepsilon^2E_Z]\psi_Z(\varepsilon\,\cdot)=0.
\]
Multiplication of its KS lift by \(4|y|^2\) gives
\[
Q_\varepsilon=P_0+B_\varepsilon,\qquad
P_0=-\Delta_y-4|y|^2\Delta_z,
\]
\[
B_\varepsilon
=-8\varepsilon Z+
8\varepsilon |y|^2\left(-\frac Z{|z|}
+\frac1{|K(y)-z|}\right)
-8\varepsilon^2E_Z|y|^2.
\tag{K1}
\]
No pair denominator remains in the lifted zero-order coefficient; the other two denominators stay separated from zero on this chart.

Use Grušin's \(m=2,\delta_G=1\), transverse dimension four and tangential dimension three. His index set is
\[
\mathcal M=\{(\alpha,\beta,\gamma):
|\alpha|+|\beta|\le2,\quad
2\ge|\gamma|\ge|\alpha|+2|\beta|-2\}.
\tag{K2}
\]
The operator belongs to this class: \(-\Delta_y\) uses \((|\alpha|,|\beta|,|\gamma|)=(2,0,0)\), the second term uses \((0,2,2)\), and \(B_\varepsilon\) uses \((0,0,0)\). The frozen principal operator is independent of \(\varepsilon\). Its ordinary symbol is
\[
|\eta|^2+4|y|^2|\xi|^2>0
\quad(y\ne0,\;(\eta,\xi)\ne0).
\]
At \(|\xi|=1\), its transverse realization is \(-\Delta_y+4|y|^2\). It has no nonzero Schwartz kernel: integration against the conjugate of a putative kernel vector yields the sum of the nonnegative quantities \(\|\nabla v\|_2^2+4\||y|v\|_2^2\). Its oscillator bottom is eight. Thus both frozen conditions hold with a scale-independent model.

Choose one sufficiently small fixed bicylinder about \((0,z_0)\), with a larger analytic neighborhood that avoids \(z=0\) and \(K(y)=z\). All real centers needed on a normalized shell form a compact set. Holomorphic branches of the two reciprocal square roots exist on a common small complex neighborhood. Hence there are finite \(C_B,A_B\), independent of \(0<\varepsilon\le1\), with
\[
\sup|D^\mu B_\varepsilon|
\le\varepsilon C_B A_B^{|\mu|}|\mu|!.
\tag{K3}
\]
This uses explicit separation of the other pair distances, not analyticity at an arbitrarily small physical patch.

Let
\[
\mathcal N(v;U)
=\sum_{\mathcal M}\|y^\gamma D_z^\beta D_y^\alpha v\|_{L^2(U)}.
\]
On a sufficiently small fixed bicylinder \(U\), Grušin's (5.5) for \(P_0\) gives a constant \(C_0\) such that
\[
\mathcal N(v;U)\le C_0\|P_0v\|_2
\qquad(v\in C_c^\infty(U)).
\tag{K4}
\]
The summand \(\|v\|_2\) belongs to \(\mathcal N\). Consequently, when
\(\varepsilon C_0C_B\le1/2\),
\[
\mathcal N(v;U)\le2C_0\|Q_\varepsilon v\|_2.
\tag{K5}
\]
Thus the common compact-support estimate does not require a new parameter-dependent parametrix.

## The finite initial norms: an explicit route, not an omitted assumption

For an inhomogeneous solution \(Q_\varepsilon u=f\), the factorial induction must start from norms proportional to the size of \(u\) and \(f\), uniformly in \(\varepsilon\). Merely knowing each \(u\) is analytic does not supply this.

A finite-order bootstrap can be made on a fixed sequence of nested bicylinders:

1. Testing the equation against \(\chi^2\bar u\), with smooth compactly supported \(\chi\), controls
\(\|\chi\nabla_yu\|_2+\|\chi|y|\nabla_zu\|_2\)
by \(\|u\|_2+\|f\|_2\). All coefficient and cutoff constants are uniform.
2. The commutator \([P_0,\chi]u\) contains only \(\nabla_yu\) and \(|y|^2\nabla_zu\), now controlled. Apply (K5) to \(\chi u\). In particular, \(\partial_zu\) and all \(\partial_y^2u\) are controlled, since their corresponding unweighted terms belong to (K2).
3. Tangential differentiation commutes with \(P_0\):
\[
Q_\varepsilon D_z^\beta u
=D_z^\beta f-
\sum_{0<\eta\le\beta}{\beta\choose\eta}
(D_z^\eta B_\varepsilon)D_z^{\beta-\eta}u.
\]
Repeating steps 1 and 2 controls any fixed finite number of tangential derivatives, with a finite, scale-independent constant.
4. The equation
\[
-\Delta_yu
=4|y|^2\Delta_zu-B_\varepsilon u+f
\]
and interior elliptic estimates in \(y\), integrated in the spectator parameter \(z\), then recover any fixed number of \(y\)-derivatives. A finite reserve of tangential derivatives pays for the two-derivative shifts. Fixed finite orders, for example thirty, suffice for the initial orders in Grušin's \(r_0=2(3+1)=8\) induction and the later Sobolev embedding in dimension seven.

This argument does not presume analytic dependence of \(u\) on \(\varepsilon\). It uses a common maximal estimate, a bounded coefficient family, and finitely many nested domains. The final all-order estimate is obtained only by the factorial induction, not by repeatedly applying this finite-order bootstrap with uncontrolled constants.

## Source of the small amplitude

Let \(c=\psi_Z(0)\), and put
\[
u_\varepsilon(y,z)
=\frac{\psi_Z(\varepsilon K(y),\varepsilon z)-c}{\varepsilon}.
\tag{K6}
\]
Local Lipschitz regularity gives a common \(L^\infty\), hence \(L^2\), bound on a fixed KS chart. Since \(Q_\varepsilon c=B_\varepsilon c\),
\[
Q_\varepsilon u_\varepsilon=-c\,B_\varepsilon/\varepsilon,
\tag{K7}
\]
whose analytic coefficient/source bounds are uniform by (K3). This is the appropriate input for a uniform factorial estimate. Applying a homogeneous estimate to \(\psi_Z(\varepsilon\,\cdot)\) without subtracting \(c\) would miss the required vanishing amplitude.

Uniform lifted Taylor coefficient bounds can then be descended through the quantitative proof of Proposition 4.4, and rotational invariance must be used to obtain distance-coordinate derivative bounds. This last invariant-coordinate step is a separate part of the main RWA proof, not supplied just by the KS theorem.

The extraction term has rescaled form
\[
q(\varepsilon X)\log\rho(\varepsilon X)^2
=\varepsilon^2q(X)\,[2\log\varepsilon+\log\rho(X)^2].
\]
On a normalized shell, \(\rho(X)^2\) is bounded away from zero. Its distance-coordinate analytic norm is therefore
\(O(\varepsilon^2(1+|\log\varepsilon|))=O(\varepsilon)\).
The analytic cusp multiplier also has a common radius after rescaling. Thus a scale-uniform distance estimate of size \(O(\varepsilon)\) suffices for the user's exact \(0<\sigma<1\) target, without assuming a convergent Fock expansion.

## Audit boundary

The cited papers alone, read only at theorem-statement level, do not assert RWA. The quantitative route above explains what must be checked in a new instantiation: the common estimate (K5), finite initial norms, the all-order induction, quantitative KS descent, and invariant-distance descent on a finite normalized-shell cover. No numerical experiment, empirical rate, or generic hp-approximation theorem enters any of these steps.

