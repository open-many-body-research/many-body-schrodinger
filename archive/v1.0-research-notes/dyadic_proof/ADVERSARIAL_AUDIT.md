> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Adversarial audit of the prescribed dyadic dictionary

This audit concerns only
\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
 e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\rm sym},\qquad Z\ge2.
\]
There is no change of nodes, polynomial degree, Hamiltonian, or norm. No numerical RATE data are used.

## 1. The angular logarithm does not force negative powers in the final witness

Put \(S=r+s\), \(q=x_1\cdot x_2=(r^2+s^2-u^2)/2\), and
\(a=2rs/S^2\). Away from the six-dimensional origin,
\[
0\le a\le\tfrac12,\qquad
\log(r^2+s^2)=2\log S+\log(1-a)
=2\log S-\sum_{k=1}^\infty \frac{a^k}{k}.
\]
Thus the actual quadratic angular factor is retained. Replacing the physical logarithm by only \(\log S\) would be an unjustified omission; the series above supplies the needed exact decomposition.

**PROVEN:** the angular series converges geometrically in the physical global \(H^2(\mathbb R^6)\) norm after multiplication by \(q e^{-ZS}\). Here and below the norm is
\(\|f\|_{H^2,*}^2=\|f\|_2^2+\|\nabla f\|_2^2+\|D^2f\|_{F,2}^2\), equivalent to the usual \(H^2\) norm by fixed constants.

An explicit bound is as follows. Define
\[
M_d(Z)=\left[\frac{8\pi^2}{15}
 \frac{(2d+5)!}{(2Z)^{2d+6}}\right]^{1/2},
\quad
C_Z=32M_0(Z)+(2+8Z)M_1(Z)+(1+Z+Z^2)M_2(Z).
\]
For every integer \(K\ge0\),
\[
\left\|q e^{-ZS}\left(\log(1-a)+
 \sum_{k=1}^K\frac{a^k}{k}\right)\right\|_{H^2,*}
\le C_Z(K+5)2^{-K}. \tag{A1}
\]

### Complete derivative proof of (A1)

For \(r,s>0\), direct differentiation gives
\[
a_r=\frac{2s(s-r)}{S^3},\quad
a_{rr}=\frac{4s(r-2s)}{S^4}.
\]
Consequently
\[
|a_r|,|a_s|\le2/S,\qquad
|a_{rr}|,|a_{ss}|\le8/S^2,\qquad |a_{rs}|\le12/S^2.
\]
Let \(b=a^k\), \(k\ge1\). The chain rule yields
\[
|b_r|,|b_s|\le4kS^{-1}2^{-k},\quad
|b_{rr}|,|b_{ss}|\le16k^2S^{-2}2^{-k},\quad
|b_{rs}|\le24k^2S^{-2}2^{-k}.
\]
The Cartesian derivatives of \(F_k=qb\) have, for example,
\[
\nabla_1F_k=x_2b+qb_r e_1,
\]
\[
D_{11}^2F_k=(x_2\otimes e_1+e_1\otimes x_2)b_r
 +q\left(b_{rr}e_1\otimes e_1
 +\frac{b_r}{r}(I-e_1\otimes e_1)\right),
\]
where \(e_1=x_1/r\). There are symmetric formulas for the second electron and the mixed block. The bounds \(|q|\le rs\), \(rs\le S^2/4\) imply
\[
|F_k|\le\tfrac14 S^2 2^{-k},\qquad
|\nabla F_k|\le2(k+1)S2^{-k},\qquad
\|D^2F_k\|_F\le32k^2 2^{-k}. \tag{A2}
\]
For clarity, the two diagonal Hessian blocks are each bounded by
\((4k^2+14k)2^{-k}\le18k^2 2^{-k}\); the mixed block is bounded by
\((2+4k+6k^2)2^{-k}\le12k^2 2^{-k}\). The full Frobenius bound follows from
\(2(18)^2+2(12)^2=936<32^2\).

The apparent \(1/r\) and \(1/s\) terms are not discarded: the factor \(|q|\le rs\) cancels them in these estimates. At the origin, (A2) gives \(F_k=O(S^2)\), \(\nabla F_k=O(S)\). At a nonzero pair axis the function and first derivatives have matching traces. Integration by parts off tubes of radius \(\varepsilon\) around the codimension-three axes, and off a radius-\(\varepsilon\) ball at the origin, has vanishing boundary contributions as \(\varepsilon\downarrow0\). Thus the displayed locally bounded second derivatives are also the distributional derivatives. No interface delta is being omitted.

For the exponential product, \(|\nabla S|=\sqrt2\) and
\(\|D^2S\|_F=(2/r^2+2/s^2)^{1/2}\). The stronger bound \(|F_k|\le rs2^{-k}\) gives
\(|F_k|\|D^2S\|_F\le\sqrt2 S2^{-k}\). Product differentiation, with deliberately enlarged constants, therefore yields
\[
\|q a^k e^{-ZS}\|_{H^2,*}
\le C_Z(k+1)^2 2^{-k}. \tag{A3}
\]
The radial integral used here is exact:
\[
\|S^d e^{-ZS}\|_2^2
=16\pi^2\int_0^\infty\int_0^\infty
 r^2s^2(r+s)^{2d}e^{-2Z(r+s)}\,dr\,ds
=M_d(Z)^2.
\]
The passage from the series to the logarithm is valid in \(H^2\) by absolute convergence of (A3) after division by \(k\), and pointwise away from the origin by the elementary power series. Finally,
\[
\sum_{k>K}\frac{(k+1)^2}{k}2^{-k}
\le\sum_{k>K}(k+3)2^{-k}=(K+5)2^{-K},
\]
which proves (A1).

## 2. A legal route from the angular terms to the exact nodes

For \(k\ge1\),
\[
q a^k e^{-ZS}
=\frac{2^k q(rs)^k}{(2k-1)!}
 \int_Z^\infty (\lambda-Z)^{2k-1}e^{-\lambda S}\,d\lambda. \tag{A4}
\]
This is an identity for positive \(S\). It is not a dictionary witness, because the integral is continuous. A proof must discretize (A4) and control its derivatives.

Taylor expansion of the exponential on a dyadic panel about an allowed node
\(\lambda_j=Z2^j\) produces only terms
\[
q(rs)^k S^\ell e^{-\lambda_j S}.
\]
Every such term is a symmetric ordinary distance polynomial times the prescribed exponential. Its consumed dictionary index is exactly
\[
2k+2+\ell+2j. \tag{A5}
\]
There is no forbidden negative-power basis element in this final expression. A proof which retains \(S^{-2k}\) in the final witness, or uses a free panel midpoint as an exponential node, would fail the requested dictionary constraint. Likewise, a Taylor error bound uniform only for fixed \(k\) does not justify increasing angular order.

**PROVEN:** the completed construction in `ANGULAR_LEMMA.md` closes both finite estimates, uniformly in increasing \(k\). It uses panels centered at the permitted nodes, with interval radius at most \(\lambda_j/2\), and the complex Cauchy circle of radius \(3\lambda_j/4\), entirely in the right half-plane. The allocation \(K=m\), Taylor degree \(P=16m\), and largest node index \(J=4m\) consumes exactly \(26m+2\) in (A5). The explicit rational witness has global angular-component error bounded by
\[
(9\widetilde C_Z+2D_Z)e^{-(\log2)n/52},
\]
where \(\widetilde C_Z\) is the above \(C_Z\) with 64 in place of 32, and
\(D_Z=63\cdot10^6\cdot17^8\cdot11^{11}Z^{-3}\).

Independent checks of that proof included its Cartesian derivative constant 12, the complex parameter norm estimate (A6), the factorial ratio (A10), all tail sums, and the degree/all-index conversion. In (A6), direct norm bookkeeping gives the numerical factor
\(12\cdot3\cdot7\cdot25\cdot32=201600<10^6\), so its stated constant is conservative. The identity \(72(2/3)^{16}<1/8\) justifies the retained exponential decay despite growth of the angular order.

The separate radial component construction in `DYADIC_RADIAL_LEMMA.md` was independently checked through (R1)–(R10): the scalar Taylor remainder and its first two derivatives, factorial weights, panel ratios, singular-head cancellation, scale tail, and exact node/degree accounting all hold as written. Since
\(q e^{-ZS}\log\rho^2=2[q e^{-ZS}\log S+q e^{-ZS}\log(\rho/S)]\), the two proved approximants sum inside the same \(V_n^{(Z)}\). Thus the damped physical quadratic logarithm has a global \(H^2\) exponential rate in the exact dictionary. This is not a RATE theorem for the ground state.

## 3. Obstruction checks

**PROVEN:** the fixed finite exponent obstruction in the prior Theorem C cannot be applied with the same constants to this expanding set. In the inverse estimates its largest exponent grows like \(2^{n/2}\). Substituting that scale into a proof designed for a fixed set changes the conclusion. A lower bound of the form \(e^{-Cn}\) also would not exclude a proposed upper bound \(Ce^{-c\sqrt n}\).

**PROVEN:** the maximal available scale \(Z2^{\lfloor n/2\rfloor}\) is not by itself an obstruction for a homogeneous quadratic logarithm in six-dimensional \(H^2\). The norm of its second derivatives on a ball of radius \(\varepsilon\) is of order at most \(\varepsilon^3(1+|\log\varepsilon|)\), so ignoring scales below \(e^{-cn}\) is compatible with every slower stretched-exponential target. This observation is not a witness construction.

**OPEN:** no rigorous lower bound excluding every stretched-exponential rate for this exact dictionary has been found. Angular degree and dyadic scale can both increase with the budget; a missing-mode assertion based only on finite angular order or finite exponent sets would be invalid.

## 4. Scope and localization traps

The function \(q e^{-ZS}\log(r^2+s^2)\) retains the verified physical homogeneous quadratic logarithm, with an explicit admissible damping factor whose value at the origin is one. Proving a rate for it is a leading-singularity gate. It does not prove a rate for the entire physical factor
\(e^{F_1}\Phi\,q\log(r^2+s^2)\), nor for the eigenfunction. The nonconstant \(\Phi\) is only as regular as the cited physical theorem actually guarantees; a \(C^{1,1}\) factorization is not an all-order weighted derivative estimate.

An external cutoff may be used to define a local comparison norm or a target supported in a fixed neighborhood only if its approximation role is accounted for. Multiplying the final witness by a cutoff changes the dictionary. Independently constructing an interior witness and an exterior witness is not a global approximation unless their sum is controlled in both regions. Exponential decay of the exact bound state alone does not bound the exterior tail of a high-degree polynomial-exponential approximant.

Finally, the rational Gram coefficient estimate bounds coefficient bit length for a normalized vector already known to lie in the finite dictionary. It does not prove the missing approximation theorem; conversely, the possibility of coefficients of size \(2^{\operatorname{poly}(n)}\) is not an exponential-bit-cost obstruction.

## 5. Final independent composition and exterior-constant audit

**PROVEN — paper proof only:** the completed `LEADING_SINGULARITY_THEOREM.md` was checked through (L1)–(L15). In particular, the radial small-index constants in (L10), combination of the two components without adding their dictionary indices, local Hardy multiplier matrix of Frobenius norm \(\sqrt{87/4}<5\), Taylor remainder through two derivatives, allocation \(N+L=n\), zero witnesses at the remaining small indices, radius \(D\) versus \(D/2\), and the explicit \(|E_Z|\) term in the shifted local graph estimate all check. The final witnesses are globally in the prescribed operator domain. Only their error theorem after the physical cusp multiplier is local; no unsupported global multiplier estimate is used.

**PROVEN — paper proof only:** the completed `EXTERIOR_CONSTANTS.md` was independently checked through (X1)–(X7) and its inverse-weight argument. The supporting IMS/weighted-form calculation (P9)–(P10) yields the displayed \(K_0=161\,3^{32}/159\): the exterior corrections are \(97Z^2/2048\), and subtraction of the weight cost leaves \(159Z^2/2048\). The Young inequality in (X4), weighted first-derivative bound (X5), product/domain step (X6), graph-to-\(H^2_*\) estimate (X7), and inverse-weight matrix all have the stated constants. In (X7), Plancherel identifies the full Frobenius Hessian norm with the Laplacian norm; its final coefficient \(6b^2+2\) safely enlarges \(6b^2+3/2\). The inverse-weight matrix has squared Frobenius norm exactly \(3+5a^2+(a\sqrt6+a^2)^2\), as required.

These checks establish the stated local component theorem and the true physical eigenfunction's exterior \(H^2\) tail. They do not bound the exterior tail of a locally fitted dictionary witness, supply a forbidden cutoff/partition in that witness, or prove the normalized global graph RATE. No Lean verification is claimed for these analytic audits.
