> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Physical regularity audit for the prescribed dyadic dictionary

This audit concerns only the fixed two-electron atomic operator
\[
H_Z=-\tfrac12(\Delta_{x_1}+\Delta_{x_2})-Z/r-Z/s+1/u,
\quad Z\in\mathbb Z,\ Z\ge2,
\]
where \(r=|x_1|,s=|x_2|,u=|x_1-x_2|\), \(S=r+s\), \(\rho^2=r^2+s^2\), and \(q=x_1\cdot x_2=(r^2+s^2-u^2)/2\). The normalized positive spatial ground state is denoted by \(\psi\); the spin singlet is understood. Ground existence, simplicity, and \(\psi(0)>0\) use the already recorded atomic arguments, rather than a new spectral assertion in this audit. No new rate experiment was run.

## Exact primary-source inputs

**PROVEN.** Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Sørensen, [math-ph/0312060](https://arxiv.org/pdf/math-ph/0312060), Theorem 1.1, equations (1.8)–(1.12), DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6), treats locally integrable distributional Coulomb eigenfunctions. For kinetic coefficient one it gives \(\psi=e^{F_2+F_3}\Phi\), with \(\Phi\in C^{1,1}_{\rm loc}\), \(F_2=-\sum_iZ|x_i|/2+\sum_{i<j}|x_i-x_j|/4\), and \(F_3=(2-\pi)\sum_{i<j}Z(x_i\cdot x_j)\log(|x_i|^2+|x_j|^2)/(12\pi)\). Its Theorem 1.4 and equation (1.20) provide second-derivative estimates after bounded cutoff factorization. They do not give all-order derivative estimates. The stated optimality concerns a universal factor across solutions, not an impossibility theorem for the particular ground state.

**PROVEN.** The same authors, [0806.1004](https://arxiv.org/pdf/0806.1004), Theorem 1.4, DOI [10.1007/s00220-008-0664-5](https://doi.org/10.1007/s00220-008-0664-5), assumes a distributional eigenfunction in \(W^{1,2}\) and proves analytic-plus-distance-times-analytic decompositions near an isolated electron–nucleus or electron–electron collision. Its collision sets exclude all simultaneous collisions. Equations (1.12)–(1.13) provide Cartesian analytic coefficients on neighborhoods of those sets. Neither their radii nor factorial derivative constants are quantified uniformly while approaching a simultaneous collision. Its proof uses analytic hypoellipticity after a Kustaanheimo–Stiefel transform; this is not an all-order physical Fock expansion.

Both hypotheses apply: \(\psi\in D(H_Z)=H^2(\mathbb R^6)\subset W^{1,2}_{\rm loc}\) and solves the physical eigenvalue equation distributionally. With \(y_i=2x_i\), \(\widetilde\psi(y)=\psi(y/2)\) satisfies the kinetic-coefficient-one equation at energy \(E_Z/2\), with the same \(Z\) and electron repulsion coefficient. Thus the source conventions require an actual rescaling, not just replacing a symbol.

## Physical quadratic logarithm and legitimate local extraction

**PROVEN.** Substitution of \(y=2x\) gives
\[
\psi=e^{-ZS+u/2+\kappa_Zq\log\rho^2}\Phi,
\qquad \kappa_Z=\frac{Z(2-\pi)}{3\pi}\ne0,
\qquad \Phi\in C^{1,1}_{\rm loc}.
\tag{P1}
\]
The additional term \(\kappa_Zq\log4\) is absorbed into \(\Phi\); its exponential is smooth and bounded with bounded derivatives on each fixed ball. In particular \(\Phi(0)=\psi(0)>0\).

Let \(b=q\log\rho^2\), continuously extended by zero at the origin, and define
\[
\mathcal R=e^{ZS-u/2}\psi-\kappa_Z\psi(0)b.
\tag{P2}
\]
Then \(\mathcal R\in C^{1,1}_{\rm loc}\). This is an elementary consequence of (P1), not a new assumed regularity theorem. To check it directly,
\[
\mathcal R=\Phi+\kappa_Zb(\Phi-\Phi(0))
 +(e^{\kappa_Zb}-1-\kappa_Zb)\Phi.
\]
Writing \(\ell=\log\rho^2\), the Cartesian estimates
\[
|b|\le\tfrac12\rho^2|\ell|,\qquad
|Db|\le\rho(|\ell|+1),\qquad
\|D^2b\|_{\rm op}\le |\ell|+5
\tag{P3}
\]
follow from \(|q|\le\rho^2/2\), \(|Dq|=\rho\), \(\|D^2q\|_{\rm op}=1\), and \(\|D^2\log\rho^2\|_{\rm op}=2/\rho^2\). Multiplying the last bound by \(\Phi-\Phi(0)=O(\rho)\) removes its logarithmic divergence. The second derivatives of the exponential remainder are \(O(\rho^2(1+|\log\rho|^2))\). These bounds hold almost everywhere and define bounded weak second derivatives, with no interface delta distributions.

Common-rotation invariance of the positive ground state and of the extracted factors implies \(D\mathcal R(0)=0\). Indeed, an invariant linear functional on \(\mathbb R^3\oplus\mathbb R^3\) vanishes. Consequently
\[
\mathcal R(x)-\psi(0)=O(\rho^2),\qquad D\mathcal R(x)=O(\rho).
\tag{P4}
\]
No third or higher derivative bound is claimed.

Thus a physically faithful leading term is
\[
f_{\log}(x)=\kappa_Z\psi(0)e^{-ZS+u/2}q\log\rho^2.
\tag{P5}
\]
It retains the actual nonradial quadratic factor. This damped extension belongs to global \(H^2\): locally use (P3), the transverse-three-dimensional integrability of \(1/r,1/s,1/u\), and products; at infinity use \(u\le S\), so the damping is at least \(e^{-(Z-1/2)S}\). Equation (P1) only identifies it as the leading physical contribution locally; no global remainder decay follows from that identity.

A smooth cutoff \(\chi(\rho^2)\) equal to one on \(B_\delta\), supported in \(B_{2\delta}\), is legitimate for estimating local Sobolev norms. It does **not** belong to the prescribed dictionary. If used on approximants, the space must be explicitly written \(\chi V_n^{(Z)}\), and any conclusion is localized. Multiplication by an arbitrary \(C^\infty\) cutoff does not have a guaranteed stretched-exponential polynomial rate. Similarly, \(\Phi\) is not an analytic multiplier merely because it is \(C^{1,1}\).

## Recovering the pair factor without forbidden functions

**PROVEN conditional reduction.** Suppose a local approximation theorem has been proved for \(e^{-ZS}b\), using \(g_n\in V_n^{(Z)}\), with an \(H^2(B_{2\delta})\) bound. Then the factor \(e^{u/2}\) in (P5) can be included by the ordinary polynomial
\[
T_k(u)=\sum_{j=0}^k\frac{(u/2)^j}{j!}.
\]
For every fixed ball, its scalar errors through derivative order two are bounded by a constant times \(C_\delta^k/(k-2)!\). The physical Hessian of a scalar function of \(u\) adds its first derivative divided by \(u\), whose multiplication is controlled by the local Hardy inequality. Thus multiplication by \(T_k(u)\) has an \(H^2\) operator bound uniform in \(k\) on nested fixed balls, and replacing \(e^{u/2}\) by \(T_k\) contributes a factorially small local \(H^2\) error on the explicit target.

The exact index budget is
\[
T_k g_n\in V_{n+k}^{(Z)}:
\quad \deg(T_kP_j)\le n+k-2j.
\]
Taking \(k\) proportional to \(n\) preserves every stretched-exponential order already proved for the base logarithm, after a fixed index rescaling. No extra exponents, inverse powers, or logarithmic basis functions are introduced. Local Hardy control here is applied to a smooth cutoff on the larger ball, so no unsupported zero boundary condition on \(B_\delta\) is imposed.

The premise is now supplied by the radial and angular component proofs.
[LEADING_SINGULARITY_THEOREM.md](LEADING_SINGULARITY_THEOREM.md) gives the
combined physical estimate with explicit constant and rate \(2^{-n/104}\).

## Angular decomposition: what it resolves and what it does not

**PROVEN.** For \(S>0\), the exact symmetric identity is
\[
\log\rho^2=2\log S-
\sum_{k=1}^{\infty}\frac{(2rs)^k}{kS^{2k}},
\qquad 0\le\frac{2rs}{S^2}\le\frac12.
\tag{P6}
\]
It is the requested \(\log\rho=\log S+\log(\rho/S)\) decomposition with an angular expansion uniformly away from its logarithmic branch point. Angular truncation itself is exponentially accurate in the physical local \(H^2\) norm after multiplication by \(q\). For completeness, with \(z=2rs/S^2\) and \(T_K(z)=\sum_{k>K}z^k/k\),
\[
|T_K|\le\frac{2^{-K}}{K+1},\quad
|T_K'|\le2^{1-K},\quad
|T_K''|\le 2^{2-K}(K+1).
\]
Since distance derivatives satisfy \(|\partial^\nu z|\le C_\nu S^{-|\nu|}\) for \(|\nu|\le2\), and \(q\) is degree two,
\[
|\partial^\nu(qT_K(z))|
\le C(K+1)2^{-K}S^{2-|\nu|},\quad |\nu|\le2.
\]
The Cartesian lift adds at most a constant times
\(S(1/r+1/s+1/u)\) in the Hessian estimate. Its squared integral on a fixed six-dimensional ball is finite, so
\[
\|qT_K(z)\|_{H^2(B_\delta)}
\le C_\delta(K+1)2^{-K}.
\tag{P7}
\]
The same conclusion holds after the fixed cusp exponential multiplier by the preceding product estimates.

**PROVEN angular representation.** The negative powers in (P6) are eliminated by the explicit rational witness in [ANGULAR_LEMMA.md](dyadic_proof/ANGULAR_LEMMA.md), equations (A4)–(A14). It represents \(e^{-ZS}S^{-2k}\) by a Laplace integral, divides the parameter into contiguous bands centered at precisely \(Z2^j\), and integrates a Taylor polynomial on each band. With \(K=m,P=16m,J=4m\), every final term is
\(e^{-Z2^jS}q(rs)^kS^b\), has ordinary symmetric distance degree \(2+2k+b\), and lies in \(V_{26m+2}^{(Z)}\). All coefficients are rational, with polynomial bit length for fixed \(Z\). No inverse powers survive in the witness. That theorem gives a global physical \(H^2\) error at most \(C_Z2^{-n/52}\) for \(e^{-ZS}q\log(\rho/S)\). Thus the angular representation obligation is closed. The physical multiplier and combined leading term are accounted for separately in the leading-singularity theorem; this component result does not approximate the nonconstant physical remainder.

## Pair collisions and the first physical derivative question after the gate

**PROVEN structure, OPEN rate.** At \(r=0\), \(s>0\), the actual eigenfunction has the Cartesian analytic decomposition \(\psi=A+rB\); there are analogous formulas \(A'+sB'\) and \(C+uD\) on the other isolated collision sets. The distance factors are allowed by the dictionary, and their physical second derivatives are locally square integrable. This checks compatibility with the operator domain. It does not construct one dictionary approximation valid simultaneously in all three neighborhoods.

The qualitative conversion to analytic distance coordinates on a fixed patch can be made explicit. Near \(r=0,s=s_0>0\), choose an analytic rotation sending \(x_2\) to \(se_3\), and write \(x_1=(y_1,y_2,z)\). Uniqueness of the analytic-plus-distance decomposition makes its two analytic coefficients invariant under rotations in the \((y_1,y_2)\) plane. In their convergent analytic Taylor series, this leaves only powers of \(y_1^2+y_2^2\), \(z\), and \(s-s_0\). Substitute
\[
z=\frac{r^2+s^2-u^2}{2s},\qquad
 y_1^2+y_2^2=r^2-z^2.
\]
The denominator is harmless on a sufficiently small fixed patch with \(s\ge s_0/2\). Thus \(\psi\), including its factor \(r\), has a real-analytic extension in the ordinary distance variables on this patch.

The uniqueness used here follows by restricting a putative analytic identity
\(A(x)+|x|B(x)=0\) to each line \(x=tv\). Analyticity continues
\(A(tv)=-t|v|B(tv)\) from positive to negative \(t\), where the original
identity gives the opposite sign. Thus \(B(tv)=0\), and then \(A(tv)=0\).
Fixing the other coordinates proves uniqueness on the local collision
patch, justifying the invariance of the separate analytic coefficients.

Near \(u=0\), use \(y=x_1-x_2\) and \(t=(x_1+x_2)/2\). Here
\[
|t|=\sqrt{(r^2+s^2)/2-u^2/4}>0,\quad
\frac{y\cdot t}{|t|}=\frac{r^2-s^2}{2|t|},\quad
|y_\perp|^2=u^2-\frac{(r^2-s^2)^2}{4|t|^2},
\]
and the same planar-rotation argument applies. Away pair collisions, ordinary Cartesian analyticity and the same invariant coordinates cover collinear configurations. This also establishes qualitative analyticity across the nonvertex perimetric boundary strata.

For exchange symmetry, use local invariant variables \(S,(r-s)^2,u\). At \(r=s\), the analytic Taylor expansion in \(r-s\) is even; away it, the analytic square-root branch together with the exchanged patch yields the same local analytic function of \((r-s)^2\). A Taylor polynomial of degree \(k\) in these invariant variables has ordinary distance degree at most \(2k\). Apply this to \(e^{ZS}\psi\). On a smaller fixed patch, analytic Cauchy estimates give symmetric polynomials \(P_k\) and \(\theta\in(0,1)\) with distance-derivative errors through order two at most \(C\theta^k\). Hence \(e^{-ZS}P_k\in V_{2k}^{(Z)}\). The inverse-distance terms in the Cartesian Hessian are square integrable on the patch, so the physical local \(H^2\) error is also at most \(C'\theta^k\).

This is a fixed-patch existence statement; its constants depend on the chosen patch. The two remaining issues are the uniform quantitative bounds as the patches approach \(S=0\), and an admissible global polynomial/exponential construction which joins their approximants. Neither follows from the existence of these local analytic charts. In particular, patchwise multiplying these approximants by a smooth partition of unity generally leaves \(V_n^{(Z)}\).

**PROVEN — collision-cone separation and the remaining overlap.** Fix \(0<\eta<1/3\). In the physical triangle domain with \(S>0\), the three cones
\[
\mathcal C_r=\{r<\eta S\},\qquad
\mathcal C_s=\{s<\eta S\},\qquad
\mathcal C_u=\{u<\eta S\}
\]
are pairwise disjoint, and even their relative closures are disjoint. If \(r,s\le\eta S\), then \(S=r+s\le2\eta S<S\). If \(r,u\le\eta S\), the triangle inequality gives \(s\le r+u\), hence \(S=r+s\le2r+u\le3\eta S<S\); the \(s,u\) case is identical. These contradictions prove the assertion. Consequently no simultaneous pair–pair overlap must be estimated away from the triple origin when these narrow cones are used. Their complementary region satisfies \(r,s,u\ge\eta S\) after the corresponding open-cone interiors are removed.

This does **not** remove pair–triple overlap. Every ball \(B_\delta\) about the triple origin meets all three cones at arbitrarily small positive \(S\); its intersection with any cone is nonempty at each sufficiently small scale. The local pair-chart constants can therefore still deteriorate in precisely these intersections. On fixed annuli \(S\in[t,2t]\), separated compact angular pieces can be used, but their physical size shrinks with \(t\). Joining their approximants to the triple approximation still requires quantified scale dependence and an admissible construction inside \(V_n^{(Z)}\). Separation alone supplies neither, and a partition of unity remains an analytic device, not an automatically permitted dictionary factor.


A precise next **physical regularity** lemma, now that the explicit leading-term gate is closed, is the following refinement of the old LPWA question. It is deliberately not stated as sufficient for global RATE, because global approximation by the fixed dyadic family and exterior matching would still need proofs.

**OPEN — reduced remainder derivative bound.** For every fixed integer \(Z\ge2\), let \(\mathcal R\) be (P2) and let
\[
\widehat{\mathcal R}(a,b,c)
=\mathcal R(x_1,x_2),\quad
r=b+c,\ s=a+c,\ u=a+b,
\]
well defined by rotational invariance. Do there exist \(\delta,C,A>0\) and \(0<\sigma<1\) such that \(\widehat{\mathcal R}\) extends real analytically across each nonvertex boundary stratum of the closed octant with \(0<S=a+b+2c<\delta\), and
\[
\big|\partial^\nu[\widehat{\mathcal R}-\psi(0)](a,b,c)\big|
\le CA^{|\nu|}|\nu|!S^{\sigma-|\nu|}
\tag{P8}
\]
for every multi-index \(\nu\in\mathbb N_0^3\) and every such point? The derivatives on the boundary mean derivatives of those extensions. This deliberately weak positive exponent asks only for what the next approximation step needs. The stronger, already proved quadratic-size bound (P4) is retained; no all-order estimates or convergent physical Fock series are inferred from it.

The qualitative nonvertex analytic extensions in (P8) follow from the preceding invariant-coordinate argument; the uniform all-order inequality is the missing assertion. Neither primary source establishes that inequality. Their fixed-order \(C^{1,1}\) and isolated-pair analyticity conclusions also do not refute it. This is one exact quantitative lemma to hand to a specialist, not a replacement name for all remaining global steps.


## Exterior decay: complete elementary bound and its limit

The targeted primary Froese–Herbst paper was identified as *Exponential bounds and absence of positive eigenvalues for N-body Schrödinger operators*, DOI [10.1007/BF01206033](https://doi.org/10.1007/BF01206033). Its abstract and author bibliographic record were accessible; the full primary PDF endpoints failed. Agmon's [1982 book, Chapter 4](https://www.jstor.org/stable/j.ctt13x1d8z.7) was likewise access restricted. No unread theorem statement from either is imported. The following proof supplies exactly the physical decay needed here.

**PROVEN — exterior quadratic form bound.** If \(f\in H^1(\mathbb R^6)\) vanishes on \(\rho<R\), then
\[
\mathfrak h_Z[f]\ge
\left[-\frac{Z^2}{2}-\frac{3Z}{2R}-\frac1{2R^2}\right]\|f\|_2^2.
\tag{P9}
\]
Use the IMS partition \(\eta_1=r/\rho,\eta_2=s/\rho\); on the support under consideration these are Lipschitz, their squares sum to one, and
\(\sum_i|\nabla\eta_i|^2=\rho^{-2}\) almost everywhere. In the \(\eta_1 f\) form keep only the hydrogenic \(s\)-electron operator, bounded below by \(-Z^2/2\), the remaining attraction \(-Z/r\), and discard nonnegative kinetic and repulsion terms. Reverse the roles in the other piece. The remaining attractions sum to
\(-Z\int S\rho^{-2}|f|^2\), bounded below by \(-3Z/(2R)\|f\|^2\), since \(S\le\sqrt2\rho\le3\rho/2\). The IMS correction is at most \(\|f\|^2/(2R^2)\). Approximation in the form domain justifies these identities without imposing new boundary conditions.

**PROVEN — exponential norm bound with an explicit rate.** Set
\[
a=Z/4,\qquad R_0=32/Z,\qquad
K_0=\frac{161\,3^{32}}{159}.
\]
Then
\[
\|e^{a\rho}\psi\|_2^2\le K_0.
\tag{P10}
\]
Indeed, the already established variational bound gives
\(E_Z\le U_Z=-Z^2+5Z/8\), and for \(Z\ge2\),
\[
-Z^2/2-E_Z\ge Z^2/2-5Z/8\ge3Z^2/16.
\]
At \(R_0\), the exterior correction in (P9) is \(97Z^2/2048\). Let \(\chi\) be the linear radial ramp from zero to one on \([R_0,2R_0]\), and let \(F_N=a\min(\rho,N)\), with \(N\ge2R_0\). For \(w_N=\chi e^{F_N}\psi\), the weak eigenfunction identity gives
\[
\mathfrak h_Z[w_N]-E_Z\|w_N\|^2
=\tfrac12\int|\nabla(\chi e^{F_N})|^2|\psi|^2
\le a^2\|w_N\|^2+
\int e^{2F_N}|\nabla\chi|^2|\psi|^2.
\]
This follows by testing with \((\chi e^{F_N})^2\psi\); bounded multipliers and form approximation justify the test. The last integral is at most \(3^{32}/R_0^2\), because on its support \(2F_N\le4aR_0=32\) and \(e<3\). The difference between the exterior lower coefficient, \(E_Z\), and \(a^2\) is at least \(159Z^2/2048\). Consequently
\(\|w_N\|^2\le2\,3^{32}/159\). On \(\rho\le2R_0\), the exponential weight squared is at most \(3^{32}\). Letting \(N\to\infty\) proves (P10) by monotone convergence. All numerical constants in this estimate are exact.

**PROVEN — physical graph tail.** The same identity with \(e^{F_N}\psi\), together with the Hardy form estimate
\[
\mathfrak h_Z[v]\ge\tfrac14\|\nabla v\|_2^2-8Z^2\|v\|_2^2,
\]
gives a uniform weighted first-derivative bound. For this estimate discard repulsion and apply \(\|v/r\|\le2\|\nabla_1v\|\), its second-electron analogue, Cauchy–Schwarz, and Young's inequality. Thus \(e^{a\rho}\nabla\psi\in L^2\).

To pass to two derivatives, take the smooth weight \(W=e^{a\sqrt{1+\rho^2}}\). Its logarithmic first and second derivatives are bounded. The product rule in distributions gives
\[
H_Z(W\psi)=E_ZW\psi-\nabla W\cdot\nabla\psi-\tfrac12(\Delta W)\psi\in L^2.
\]
The previous estimates give \(W\psi\in H^1\). The weak operator associated with the Coulomb form is the self-adjoint operator with domain \(H^2\); therefore \(W\psi\in H^2\). Applying the inverse-weight product rule yields
\[
\|\psi\|_{H^2(\{\rho>T\})}\le C_Ze^{-ZT/4}.
\tag{P11}
\]
This supplies a genuine operator-domain tail estimate, rather than just an energy tail or a pointwise bound. A smooth radial cutoff at radius \(T\) has first and second derivative costs \(O(T^{-1})\), \(O(T^{-2})\), hence cutting the physical function produces the same exponential tail order for \(T\ge1\).

**OPEN dictionary transfer.** Neither the cut off physical function nor a cut off local approximant belongs to the prescribed dyadic space. In particular, the globally uncut approximants produced for the logarithmic gate may have uncontrolled tails unless separately estimated. Equation (P11) controls the true eigenfunction, not such polynomial-exponential extrapolations. It does not prove exterior approximation or a global RATE.

## Scope of this audit

**PROVEN:** the coefficient and kinetic rescaling; actual leading-term extraction; the elementary \(C^{1,1}\) remainder; local \(H^2\) domain checks; an index-respecting way to attach the electron–electron exponential cusp factor to an already proved base construction; geometric angular tail control and its rational dyadic representation; collision-cone separation; fixed-patch analytic distance approximation; the explicit physical exterior decay estimate (P10) and graph tail (P11).

**OPEN:** simultaneous scale-uniform pair approximation, the quantitative inequality in (P8), exterior approximation and admissible global gluing, the global graph RATE, and Theorem T. The angular inverse-power representation is PROVEN by the explicit dyadic witness cited above. This audit does not import a physical all-order Fock series or use the finite numerical rate fits as evidence for an asymptotic theorem.
