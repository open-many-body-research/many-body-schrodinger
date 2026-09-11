> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Resolved collision geometry and weighted analytic regularity: primary-source audit

Date: 2026-09-09. Scope: the fixed two-electron atomic remainder RWA, with ordinary half-perimetric derivatives and weight S=a+b+2c. This is a bounded theorem audit, not a new literature survey of approximation methods. No numerical experiment or Lean verification was performed.

**Audit conclusion:** none of the theorems below, as stated, discharges RWA. This conclusion concerns applicability of these sources; it is not a proof that RWA is false or unprovable by another argument. In particular, “all finite orders” and “factorial control uniformly in the order” must be kept separate.

## 1. Ammann–Carvalho–Nistor: actual many-particle collision resolution

**Primary source read:** [author preprint, Theorem 4.3, equation (3), Section 4.1](https://ammann.app.uni-regensburg.de/preprints/schrodinger/schrodinger.pdf); [arXiv:1010.1712](https://arxiv.org/abs/1010.1712); journal DOI [10.1007/s11005-012-0551-z](https://doi.org/10.1007/s11005-012-0551-z). Numbering here follows the accessible 30-page author PDF.

Hypotheses: H=-Delta+V on R^(3N), Coulomb sums b_j/|x_j|+c_ij/|x_i-x_j| (Section 4 also allows suitable smooth lifted coefficients); an L² distributional eigenfunction. Conclusion, for every integer m>=0 and a<=0:

\[
u\in\mathcal K_a^m,
\qquad
\mathcal K_a^m=\{u:r_{\mathcal S}^{|\alpha|-a}\partial^\alpha u\in L^2,
\ |\alpha|\le m\}.
\]

The weight is the resolved collision distance; locally on bounded sets it has the stated collision-distance interpretation. Iterated blowups include intersecting collision strata and produce manifolds with corners. For our operator, take N=2, b_1=b_2=-2Z, c_12=2, eigenvalue 2E_Z.

**Order/constant audit:** membership at every finite m is PROVEN. No C A^m m! estimate is asserted. Derivatives are weighted Cartesian derivatives, not ordinary reduced derivatives across collision edges. Moreover, the weight vanishes at pair collisions even when S>0. No conversion to RWA follows from this theorem.

## 2. Ammann–Mougel–Nistor: improved global resolved regularity

**Primary source read:** [arXiv:2012.13902, Theorem 1.1 and equation (6)](https://arxiv.org/pdf/2012.13902); [published open-access article, DOI 10.1007/s11005-023-01648-0](https://doi.org/10.1007/s11005-023-01648-0). Theorem 1.1 agrees in both versions.

Let F be a finite intersection-closed collection of proper linear subspaces of X=R^d, containing {0}. Resolve the collision planes and their boundaries at infinity to X_F. For a_Y smooth on X_F, set V=sum_Y a_Y/d_Y+a_X, d_Y=dist(.,Y). If u in L² solves (Delta+V)u=lambda u off the planes, then

\[
\delta_F^{|\alpha|}\partial^\alpha u\in L^2(X)
\quad\hbox{for every }\alpha,
\qquad
\delta_F=\min\{\operatorname{dist}(x,\cup F),1\}.
\]

This covers d=6 and F={0,{x_1=0},{x_2=0},{x_1=x_2}}. For our equation choose coefficients 2Z,2Z,-sqrt(2) on the three planes respectively, zero on {0} and X, and lambda=-2E_Z; the diagonal-plane distance equals u/sqrt(2).

**Order/constant audit:** global weighted Sobolev regularity, including collision intersections and infinity, is PROVEN for each order. Factorial order growth is absent. Smooth resolved coefficients do not by themselves imply analytic regularity. Pair-distance weights and ordinary half-perimetric derivatives remain a second mismatch. RWA is not a consequence.

## 3. Fournais–Sørensen: precise derivative-distance estimates

**Primary source read:** [arXiv:1803.03495, Theorem 1.1 and Corollary 1.2](https://arxiv.org/pdf/1803.03495), accessible 46-page version dated September 3, 2018.

For the 3N-dimensional atomic Coulomb Hamiltonian, a W_loc^(2,2) solution, p in (1,infinity], |alpha|>=1, and 0<r<R<1, Theorem 1.1 gives L^p derivative estimates on balls of radius comparable to lambda_alpha=min(1,dist(.,Sigma_alpha)). The constant is explicitly allowed to depend on alpha, p, r, R, E, N, Z. Corollary 1.2 includes

\[
|\partial^\alpha\psi(x)|
\le C(\alpha,R,E,N,Z)\lambda(x)^{1-|\alpha|}
\|\psi\|_{L^\infty(B(x,R))},
\quad
\lambda=\min\{1,\operatorname{dist}(x,\Sigma)\}.
\]

Our kinetic convention can be matched by y=2x and energy E_Z/2. Bounds hold away from the appropriate pair-collision set, and capture the correct fixed-order distance powers, including approaches towards intersecting sets.

**Order/constant audit:** every fixed-order estimate is PROVEN; the displayed C(alpha,...) is not bounded factorially by the theorem. Also dist(x,Sigma) can be arbitrarily smaller than S on a normalized shell. Neither replacing this weight by S nor extending ordinary derivatives to reduced collision edges is supplied. No RWA inference is justified.

## 4. Maday–Marcati: a genuine factorial theorem, but for isolated point singularities

**Primary source read:** [arXiv:2010.06923, Theorem 1, equations (3)–(7), Corollary 1](https://arxiv.org/pdf/2010.06923). The accessible 19-page preprint is dated October 14, 2020.

Theorem 1 assumes d=2 or 3, singular points separated by at least 4D, a distance weight r equal to |x-c| near each point, and

\[
\|r^{2-\epsilon+|\alpha|}\partial^\alpha V\|_\infty
\le C_V A_V^{|\alpha|}|\alpha|!,\qquad0<\epsilon<1.
\]

Its solution hypothesis is a unique H¹ solution of the coupled Laplacian/Poisson system (3), including the displayed finite polynomial couplings. For every eta<epsilon it concludes, near the singular points,

\[
|\partial^\alpha\phi_i(x)|
\le r(x)^{\min\{\eta-|\alpha|,0\}}
A^{|\alpha|+1}|\alpha|!.
\]

This is genuinely all-order with one A, uniform towards each isolated singularity. Corollary 1 specializes to negative-energy Hartree–Fock orbitals under its uniqueness hypothesis.

**Applicability:** the physical correlated eigenfunction is six-dimensional with collision planes. Reducing rotations produces a degenerate three-dimensional principal part, not the Laplacian in (3). Neither operator nor singularity hypothesis matches. The theorem controls orbitals, not the extracted correlated remainder. Its induction is a useful model, but does not discharge RWA.

## 5. Costabel–Dauge–Nicaise: factorial estimates at corners and edges

**Primary source read:** [arXiv:1002.1772, Theorem 6.8, Definition 6.4, Assumption 6.5](https://arxiv.org/pdf/1002.1772); DOI [10.1142/S0218202512500157](https://doi.org/10.1142/S0218202512500157). Numbering follows the accessible 54-page arXiv PDF. The older 46-page author PDF has different numbering.

In a three-dimensional polyhedron, the model (6.3) is a homogeneous constant-coefficient elliptic system with its stated homogeneous face boundary operators. At every edge it requires the Peetre estimate (6.10):

\[
\|u\|_{K^2_{\beta_e}(\Omega_e)}
\le C\bigl(\|f\|_{K^0_{\beta_e+2}(\Omega'_e)}
+\|u\|_{K^1_{\beta_e+1}(\Omega'_e)}\bigr).
\]

Then Theorem 6.8 gives K_beta^1 membership plus f in A_(beta+2) implies u in A_beta. Definition 6.4 requires seminorms <=C^(k+1)k!. Its anisotropic corner-edge weights include r_c^(beta_c+k)(r_e/r_c)^(beta_e+|alpha_perp|). Constants are uniform in derivative order and radial corner scale for the fixed elliptic boundary problem.

**Applicability:** the reduced Coulomb principal symbol degenerates on collinear faces; those faces are orbit-space boundaries, not an imposed elliptic boundary-value problem. No applicable Peetre estimate or compatible boundary system has been verified. Moreover, vanishing edge weights do not imply unweighted edge derivatives. Thus this real factorial theorem does not imply RWA.

## 6. Marcati–Rakhuba–Schwab: regularity is an input to approximation

**Primary source read:** [arXiv:1912.07996v1, Proposition 4, equation (43), Section 1.2.2](https://arxiv.org/pdf/1912.07996).

On Q=(0,1)^3 with a point singularity at 0, define weighted Gevrey membership using

\[
|u|_{K^s_\gamma}\le C A^s(s!)^d,
\quad s>\gamma-3/2,
\qquad d\ge1.
\]

Proposition 4 assumes gamma>=gamma_0>3/2 and this membership. It constructs a conforming hp projector with H¹ error <=C_hp exp(-b_hp ell), using degree p=c_0 ell^d; constants are independent of ell. The mesh has dimension of order ell p^3. Edges/faces of the cube are part of the approximation geometry; weighted regularity at its distinguished point is assumed.

**Applicability:** this is an approximation theorem, not a proof of physical weighted analyticity. It neither supplies RWA nor approximates in physical six-dimensional H² by the prescribed exponential dictionary. Even d=1 cannot be imported before membership and the norm/dictionary conversion are separately proved. No new approximation claim is taken from it here.

## 7. Flad–Schneider–Schulze: asymptotic smoothness in a different electronic model

**Text read:** [May 23, 2007 author preprint, mirrored PDF](https://scispace.com/pdf/asymptotic-regularity-of-solutions-to-hartree-fock-equations-s1057nj7h8.pdf), Definition 1, Proposition 1, Theorems 1–2. Published DOI [10.1002/mma.1021](https://doi.org/10.1002/mma.1021). Publisher text returned 403; the accessible item is the authors' preprint, not independently checked against the published version.

On the stretched cone R_+ x S² for three-dimensional Hartree–Fock orbitals, Definition 1 uses an asymptotic space S_P^gamma, gamma<3/2, with P={(-j,0,L_j)} and L_j spanned by spherical harmonics of degree <=j. Theorem 1 preserves this class during level shifting. Theorem 2 gives it for self-consistent solutions obtained from an initial guess in that class. Proposition 1 yields smoothness on the stretched cone and fixed-order bounds |D^beta u|<=C_beta r^(1-|beta|).

**Applicability:** no factorial growth estimate on C_beta is asserted. This is an effective one-particle Hartree–Fock problem, with isolated nuclei, not the exact two-electron triple collision. Its no-log expansion for those orbitals must not be transferred to the correlated wavefunction. It does not establish RWA.

## 8. Guo–Babuška: access limitation recorded rather than filled from secondary summaries

Located the primary publication records for the 1988/1989 pair: DOI [10.1137/0519014](https://doi.org/10.1137/0519014) and DOI [10.1137/0520054](https://doi.org/10.1137/0520054). Direct PDF access failed in this audit. Exact theorem numbers and complete hypotheses were therefore not verified and no assertion from these papers is a proof dependency. The accessible Costabel–Dauge–Nicaise theorem above provides a precise independently readable analytic-corner result with its own hypotheses; it is not used to guess statements in the inaccessible papers.

## The concrete mismatch after collision resolution

The many-body sources give the right collision geometry but no uniform factorial estimate. The factorial sources cover the wrong principal operator or assume the desired regularity. In ordinary half-perimetric coordinates, RWA asks for analyticity through every nonvertex collision edge with radius proportional to S, uniformly as S decreases. A bound for vector fields tangent to exceptional divisors, or with extra vanishing powers of the pair distance, is weaker than that request.

For example, a bound using dist(x,Sigma) has no content for ordinary transverse derivatives at r=0 with s>0. At such a point S=s remains positive, so the RWA right-hand side is finite and enforces a genuine analytic extension with a controlled radius. The change from resolved weighted derivatives to these ordinary derivatives needs a proved chart estimate; it cannot be absorbed into one unspecified constant.

**Smallest source-level missing input:** an analytic, scale-uniform estimate for the physical compatible solutions of the rescaled reduced Coulomb equation on the compact angular shell, including its collinear faces and pair-collision edges. Such an estimate must bound ordinary coordinate derivatives, not merely conormal derivatives, and its constants must be uniform in the small Coulomb coupling produced by scaling. The exact operator and the quantified missing estimate belong in the separate reduced-equation proof; none of the external statements audited here already proves it.

## Logical stress test: why infinite smoothness plus punctured analyticity is insufficient

This diagnostic is an elementary argument, **not a physical counterexample**. For 0<S<1 set

\[
f(S)=e^{-1/S^2}\sin(e^{1/S}),\qquad f(0)=0.
\]

Every fixed derivative is bounded by a finite sum of terms of the form S^(-M) exp(-1/S²+j/S), so f is C-infinity and flat at 0, real analytic away from 0, and belongs locally to every finite polynomially weighted Sobolev space.

Suppose it satisfied |f^(k)(S)|<=C A^k k! S^(sigma-k). Its Taylor series would then be bounded by 2C S^sigma on |z-S|<=S/(2A), and would coincide there with the holomorphic formula. Put z=S+i(pi/2)S². As S tends to 0, Im(e^(1/z)) has magnitude comparable to exp(1/S), so the sine factor grows double-exponentially, whereas the prefactor has only exp(-O(S^(-2))) size. This contradicts the Taylor bound. Thus the missing all-order estimate is substantive even after all finite-order smoothness has been proved.

No claim in this audit changes the existing leading-singularity theorem or Theorem T status.
