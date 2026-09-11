> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Uniform analytic estimates on nonsingular Cartesian charts

Evidence category: **paper proof**. The result concerns an actual weak
solution of a constant-kinetic elliptic equation with a bounded analytic
potential. It supplies the nonsingular local PDE input left explicit in
DISTANCE_BOUNDARY_GERMS_v1.md. It is not a Lean theorem or a proof of the
physical ground-state hypotheses.

## 1. Exact theorem and explicit constants

Fix an integer \(d\ge1\), numbers \(a,e_0>0\), and
\(0<\rho\le\min(1,a/2)\). Let the outer box, base box and final box be
\[
 U_{\rm out}=x_0+(-a-4e_0,a+4e_0)^d,\qquad
 U_0=x_0+(-a,a)^d,\qquad U_\rho=x_0+(-a+\rho,a-\rho)^d.
\]
Suppose \(B,f\in C^\infty(U_{\rm out})\), \(M,A\ge1\), \(F\ge0\), and
\[
 \|D^\eta B\|_\infty\le MA^{|\eta|}|\eta|!,\qquad
 \|D^\eta f\|_{L^2(U_{\rm out})}\le FA^{|\eta|}|\eta|!.
\]
Let \(v\in L^2(U_{\rm out})\), \(W=\|v\|_2\), satisfy the actual
distributional equation
\[
 (-\Delta+B)v=f.                                                  \tag{E1}
\]
The coefficients and functions may be complex; there is no smallness
assumption on \(M\).

The following constants are explicit and independent of derivative order:
\[
\begin{split}
 J_d&=\binom{d+2}{2},\qquad L_0=3\sqrt d/e_0,\qquad
 T_0=27d/e_0^2,\\
 E_0&=\sqrt{1+4L_0^2},\qquad
 G_0=1+E_0+(1+2L_0E_0+T_0),\\
 A_0&=G_0(1+M),\qquad
 A_1=G_0\bigl[(1+8MA^2)A_0+2A^2\bigr],\\
 H_0&=J_dA_1(W+F),\qquad S=F+H_0,\\
 C_P&=4a^2,\qquad C_0=J_d\max(C_P,\sqrt{C_P},1),\\
 C&=\max\{1,C_0\max(1,27d+M,M)\},\qquad B_0=2CA,\\
 L&=2(a-\rho),\qquad E_{\rm box}=(L^{-1/2}+L^{1/2})^d,\\
 C_*&=2B_0E_{\rm box}(2B_0/\rho)^d3^{d+1}(d+1)^d,\qquad
 A_*=(2B_0/\rho)\,3\,2^d .
\end{split}                                                       \tag{E2}
\]
Then the smooth representative of \(v\) obeys
\[
 \sup_{U_\rho}|D^\eta v|\le C_*S A_*^{|\eta|}|\eta|!.              \tag{E3}
\]
In particular \(S\le(1+J_dA_1)(W+F)\), so the result is linear in
the solution/source amplitude.

At a real point with retained box margin, Taylor's theorem gives a
holomorphic extension on the corresponding complex L1 ball
\(A_*|z-x|_1<1\), with bound
\[
 C_*S/(1-A_*|z-x|_1).
\]
On the half-radius ball the bound is \(2C_*S\). Identification with the
real solution uses the real box margin. A common complex coordinate
polydisc follows by choosing radius no greater than
\(1/(2dA_*)\) and that margin.

## 2. Weak finite initialization from L2

We first record the concrete weak elliptic gain used here. On three nested
boxes with successive half-width gap \(e_0\), take cutoffs \(\eta,\chi\)
equal to one on the middle and inner boxes, respectively, with
\[
 \|\nabla\eta\|_\infty,\|\nabla\chi\|_\infty\le L_0,\qquad
 \|\Delta\chi\|_\infty\le T_0.
\]
The same C2 quintic transition as in the preceding proofs gives these
bounds, with transition width \(3e_0/4\) and a positive support margin.

If \(-\Delta w=h\) weakly and \(w,h\in L^2\) on the outer box, write
\(W_w=\|w\|_2,H_h=\|h\|_2\). The energy estimate is
\[
 \|\eta\nabla w\|_2^2
 \le H_h^2+(1+4L_0^2)W_w^2.
\]
Indeed integration by parts gives the source pairing and one first-order
cross term; Young's inequality yields this bound. On the support of
\(\chi\), the gradient is therefore at most \(E_0(W_w+H_h)\), and
\[
 \|\Delta(\chi w)\|_2
 \le H_h+2L_0E_0(W_w+H_h)+T_0W_w
 \le(1+2L_0E_0+T_0)(W_w+H_h).
\]
The compact-support identity \(\|D^2(\chi w)\|_2=\|\Delta(\chi w)\|_2\)
now proves
\[
 \max_{|\eta|\le2}\|D^\eta w\|_{L^2(\text{inner box})}
       \le G_0(W_w+H_h).                                         \tag{E4}
\]

For initially weak \(w\), this proof is licensed by ordinary convolution
on a slightly larger local box. The Laplacian commutes with convolution;
the cutoffs have a fixed positive distance from the outer boundary.
For sufficiently small convolution radius the same energy and Hessian
estimates apply, with L2 norms bounded by the original outer norms.
Weak compactness and distributional convergence identify the limits as
the actual weak derivatives. C2 cutoffs suffice by H2 approximation.
Thus no smoothness of \(w\) or hidden high derivative bound is a premise
of (E4).

Apply (E4) first to \(v\), with \(h=f-Bv\), across the first two of the
four reserved gaps. This gives
\[
 \max_{|\eta|\le2}\|D^\eta v\|_2
       \le A_0(W+F).                                             \tag{E5}
\]
For any \(|\beta|\le2\), the distributional equation is
\[
 -\Delta D^\beta v=D^\beta f-D^\beta(Bv).
\]
On the middle box all terms on the right are L2 by (E5), and
\[
 \|D^\beta f\|_2\le2FA^2,\qquad
 \|D^\beta(Bv)\|_2\le8MA^2A_0(W+F).
\]
The product estimate uses the binomial sum \(2^{|\beta|}\le4\) and
\(\max_{|\eta|\le2}\|D^\eta B\|_\infty\le2MA^2\).
A second weak gain across the last two gaps proves
\[
 \max_{|\eta|\le4}\|D^\eta v\|_{L^2(U_0)}
       \le A_1(W+F).                                             \tag{E6}
\]
Every target of order at most four is obtained by selecting at most two
base derivatives and at most two outer derivatives. This verifies the
entire initialization, not only pure derivatives.

Repeating such finite weak gains on any compactly contained boxes shows
that \(v\) is smooth in \(U_{\rm out}\). Those higher-order constants are
used only to license the following differentiations. They do not enter
the factorial estimate.

## 3. Maximal norm and exact localization losses

For a function on a box define
\[
 N(w)=\sum_{|\beta|\le2}\|D^\beta w\|_2.
\]
There are \(J_d\) summands. For compactly supported \(w\) in \(U_0\),
Poincare in one coordinate and the energy identity give
\[
 \|w\|_2\le C_P\|\Delta w\|_2,\qquad
 \|\nabla w\|_2\le\sqrt{C_P}\|\Delta w\|_2.
\]
The full Hessian norm equals the Laplacian norm. Hence
\[
 N(w)\le C_0\|\Delta w\|_2.                                      \tag{E7}
\]
This extends by density to compactly supported H2 functions.

For \(0\le s\le\rho\), let \(U_s=x_0+(-a+s,a-s)^d\), and set
\[
 N_r(s)=\max_{|\alpha|\le r}N(D^\alpha v;U_s).
\]
Equation (E6) gives \(N_0(s),N_1(s)\le H_0\).

For \(s+e\le\rho\), choose \(\phi=1\) on \(U_{s+e}\), compactly supported
in \(U_s\), with each first derivative bounded by \(3/e\), and each
pure second derivative by \(27/e^2\). For \(|\alpha|\le r\), \(r\ge2\),
\[
 [-\Delta,\phi]D^\alpha v
 =-2\nabla\phi\cdot\nabla D^\alpha v-(\Delta\phi)D^\alpha v.
\]
In the first term move one derivative from \(\alpha\) into the outer
norm, giving an order-two derivative with base order at most \(r-1\).
If \(|\alpha|=0\), use the outer first derivative and zero base.
In the second term move two derivatives into the outer norm; if fewer
than two are present use the whole derivative as an outer term.
The corresponding base index is at most \(r-2\). Therefore
\[
 \|[-\Delta,\phi]D^\alpha v\|_2
 \le27d\bigl(e^{-1}N_{r-1}(s)+e^{-2}N_{r-2}(s)\bigr).            \tag{E8}
\]
The first coefficient is actually \(6d\), enlarged here to \(27d\).
There is no hidden derivative-order dependence in the cutoff constants.

The potential commutator satisfies
\[
 \|[B,D^\alpha]v\|_2
 \le M\sum_{j=1}^r A^j{r!\over(r-j)!}N_{r-j}(s),                 \tag{E9}
\]
by grouping the Leibniz terms according to the number \(j\) of derivatives
on \(B\). The sum of multi-index binomial coefficients at that size is
\(\binom{|\alpha|}{j}\).
The remaining undifferentiated potential term is also lower level:
\[
 \|B\phi D^\alpha v\|_2\le M N_{r-1}(s).
\]
For a nonzero \(\alpha\), move one derivative into the outer first
derivative norm; for zero \(\alpha\) use the zero base. This is the step
that removes any need to absorb a small potential.

## 4. Closed factorial recurrence

Apply (E7) to \(\phi D^\alpha v\), and use (E1), (E8), (E9) and
\(e\le\rho\le1\). The exact recurrence is
\[
 N_r(s+e)\le C\left[
 FA^r r!+e^{-1}N_{r-1}(s)+e^{-2}N_{r-2}(s)
 +\sum_{j=1}^r A^j{r!\over(r-j)!}N_{r-j}(s)\right],\quad r\ge2.
                                                                  \tag{E10}
\]
If \(S=0\), then \(v=0\). Otherwise, for a fixed integer \(\ell\ge1\),
put \(h=\rho/\ell\) and
\[
 d_r={h^r\over S}N_r((r+1)h),\qquad 0\le r\le\ell-1.
\]
For \(r=0,1\), the initialization gives \(d_r\le1\). Applying (E10)
with \(s=rh,e=h\), using nested boxes and
\(h^j r!/(r-j)!\le1\), gives
\[
 d_r\le C\left[A^r+d_{r-1}+d_{r-2}
                     +\sum_{j=1}^r A^j d_{r-j}\right]
 \le B_0^{r+1}+\sum_{j=1}^r B_0^j d_{r-j}.
\]
Induction with the exact finite sum
\[
 B_0^{r+1}+\sum_{j=1}^rB_0^j(2B_0)^{r-j+1}
       =B_0^{r+1}(2^{r+1}-1)\le(2B_0)^{r+1}
\]
proves \(d_r\le(2B_0)^{r+1}\). Choosing \(\ell=r+1\) yields
\[
 N_r(\rho)\le2B_0S\left({2B_0(r+1)\over\rho}\right)^r.            \tag{E11}
\]
For the two initial indices the same inequality follows from their
initial bound.

## 5. Explicit pointwise conversion

On an interval of length \(L\), averaging the fundamental theorem of
calculus represents point evaluation as an integral of the function plus
an integral of its first derivative. The kernel L2 norms are at most
\(L^{-1/2}\) and \(L^{1/2}\). Tensoring in \(d\) coordinates proves
\[
 \sup_{U_\rho}|w|
 \le E_{\rm box}\max_{\nu\in\{0,1\}^d}\|D^\nu w\|_{L^2(U_\rho)}.
\]
For \(|\eta|=k\), apply this to \(w=D^\eta v\) and use (E11) at
\(r=k+d\). The elementary inequality
\[
 (k+d+1)^{k+d}
 \le3^{d+1}(d+1)^d(3\,2^d)^k k!                                \tag{E12}
\]
then gives (E3) with exactly (E2). To check (E12), for \(k\ge1\) use
\(k!\ge(k/3)^k\), \((1+(d+1)/k)^k\le3^{d+1}\), and
\(k+d+1\le(d+1)2^k\). At \(k=0\) it is immediate.

Taylor's integral remainder proves agreement with the real solution on
the stated L1 radius, and geometric summation of the same derivative
bound gives the holomorphic bound in Section 1. This step does not
infer complex bounds directly from real sup bounds alone.

## 6. The actual nonsingular scaled Coulomb equation

Take \(d=6\), \(X=(X_1,X_2)\), and a compact normalized Cartesian chart
on which all three distances \(|X_1|,|X_2|,|X_1-X_2|\) are bounded
away from zero. Let \(\psi\) be the actual locally Lipschitz distributional
solution of the two-electron equation with kinetic energy
\(-\tfrac12\Delta\), and let
\[
 V(X)=-Z/|X_1|-Z/|X_2|+1/|X_1-X_2|.
\]
For a fixed scale interval \(0<\varepsilon\le\varepsilon_0\), assume
the scaled chart images stay in the common Lipschitz neighborhood. The
actual scaled function \(U_\varepsilon(X)=\psi(\varepsilon X)\)
satisfies
\[
 [-\Delta+B_\varepsilon]U_\varepsilon=0,\qquad
 B_\varepsilon=2\varepsilon V-2\varepsilon^2E.                    \tag{E13}
\]
This follows by the ordinary invertible linear scaling in distributions.
For \(a_0=\psi(0)\),
\[
 v_\varepsilon=(U_\varepsilon-a_0)/\varepsilon,\qquad
 [-\Delta+B_\varepsilon]v_\varepsilon
                   =-a_0B_\varepsilon/\varepsilon.              \tag{E14}
\]
Local Lipschitz regularity gives
\(\|v_\varepsilon\|_\infty\le L_\psi\sup|X|\) on the fixed chart.
The separated Coulomb denominators have common analytic neighborhoods
and hence common coefficient bounds; the fixed energy \(E\) is finite.
Thus (E3) and its complex extension apply with constants independent of
\(\varepsilon\), once these explicit coefficient hypotheses are supplied.
Multiplication by \(\varepsilon\) returns the common analytic amplitude
of \(U_\varepsilon-a_0\).

The pair charts were handled by weak KS removability, H12 initialization,
the Grushin recurrence and constructive coefficient descent. This lemma
supplies the remaining nonsingular Cartesian analytic estimate needed by
the coordinate and gluing theorem, with no use of qualitative elliptic
analyticity as a quantitative substitute.

The actual physical solution, its Lipschitz and rotational properties,
uniform analytic coefficient neighborhoods, spectral interpretation and
Lean formalization remain separate. Nothing here asserts an attained or
unique spectral infimum.

## 7. Preservation and comparison

Frozen target: rwa_proof/RWA_THEOREM.md section 4, SHA-256
d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660;
tag theorem-t-proof-freeze-2026-09-09.

The finite normalization and pointwise embedding follow the explicit
algebra already proved in the new GRUSHIN_FACTORIAL_RECURRENCE_v1.md,
SHA-256 5aac0a379715bda90c7eb12ff2c8af2b5c6aba2434828735a96c608c45668594.
They are reproduced above for this simpler operator, with its own norm
index set, initialization and dimension dependence.

This is a direct quantitative local estimate, not a literature novelty
claim. No inaccessible primary theorem is needed for its proof, and no
frozen or sealed artifact was changed. The auxiliary
nonsingular_elliptic_checks_v1.py checks finite integer identities and
derivative allocations; independent review is recorded separately.
