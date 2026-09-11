> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit exponential decay from exterior coercivity

Evidence category: **paper theorem**, with a conditional hydrogenic
application and an exact rational exponential-tail check.
The actual exterior lower bound is a stated premise in the abstract
part and is derived explicitly from a specified hydrogenic rank-one
comparison in the two-electron application. No ionization threshold
is used as a substitute for a bound on excited states.

## 1. Actual-domain exterior hypothesis

Let \(N\ge1\), \(Z\ge0\), and let
\(\psi\in H^2(\mathbb R^{3N};\mathbb C^{2^N})\) satisfy
\(H_{N,Z}\psi=E\psi\), \(E\in\mathbb R\), for the physical Coulomb
operator. The scalar version is included. Put
\[
 \rho(x)=\left(\sum_i|x_i|^2\right)^{1/2},\quad
 S(x)=\sum_i|x_i|,\quad U=\|\psi\|_2.
\]
Suppose there are \(R_0>0,\delta_0>0\) such that every actual H2
function \(v\) vanishing almost everywhere on \(\rho\le R_0\) obeys
\[
 \langle Hv,v\rangle-E\|v\|_2^2\ge\delta_0\|v\|_2^2.            \tag{C1}
\]
One may impose (C1) only in the fermionic subspace if \(\psi\)
is fermionic. All multipliers below preserve that subspace.
The inner products in (C1) are real, by the actual symmetric
Coulomb operator or its integration-by-parts form.
No form-domain extension of (C1) is needed in this proof.

Set
\[
 \alpha=\sqrt{\delta_0/2},\qquad
 C_\rho=e^{\alpha(R_0+1)}
                        \max(1,\sqrt{8/\delta_0})\,U.
\]
Then the actual eigenfunction has
\[
 \|\psi\|_{L^2(\rho>R)}\le C_\rho e^{-\alpha R}\quad(R\ge0),
 \qquad
 \|\psi\|_{L^2(S>R)}\le C_\rho e^{-\alpha R/\sqrt N}.             \tag{C2}
\]
This proves an exponential L2 tail from a genuine exterior operator
estimate. The estimate is not an assumption about a desired decay
rate or about the spectrum's essential threshold.

## 2. Bounded smooth weights stay in the actual H2 domain

Use the C2 quintic step \(\Theta\) from the tail-transfer proof,
with \(|\Theta'|\le2\), and let
\[
 \chi(x)=\Theta(\rho(x)-R_0).
\]
Thus \(\chi=0\) on \(\rho\le R_0\), \(\chi=1\) on
\(\rho\ge R_0+1\), and \(|\nabla\chi|\le2\).
For each finite \(L>0\) define
\[
 \vartheta_L(t)=L(1-e^{-t/L}),\qquad
 f_L(x)=\alpha\vartheta_L(\rho(x)),\qquad
 g_L=\chi e^{f_L},\qquad v_L=g_L\psi.                          \tag{C3}
\]
On \(t\ge0\), \(0\le\vartheta_L(t)\le t\),
\(0\le\vartheta_L'(t)\le1\), and
\(\vartheta_L(t)\uparrow t\) as \(L\to\infty\).
For monotonicity, differentiate in \(L\) and use
\((1+s)e^{-s}\le1\), \(s=t/L\).
In particular \(|\nabla f_L|\le\alpha\) away from zero.

Although the radial coordinate is nonsmooth at zero, \(g_L\) is
identically zero on an open ball there. For finite \(L\), the
exponential and its first two derivatives are bounded on
\(\rho\ge R_0\), including the radial \(1/\rho\) factors.
Thus \(g_L,g_L^2\in W^{2,\infty}\), and both \(v_L\) and
\(g_L^2\psi\) are actual H2 functions. This is why the smooth
bounded saturation in (C3) was chosen: the nonsmooth weight
\(\min(\rho,L)\) would in general supply only H1 without another
approximation step.

The eigenfunction equation paired with \(g_L^2\psi\) gives the
exact actual-domain identity
\[
 \langle Hv_L,v_L\rangle-E\|v_L\|_2^2
                      ={1\over2}\|(\nabla g_L)\psi\|_2^2.      \tag{C4}
\]
The product rule, integration by parts and all Coulomb terms are
licensed as in the independently reviewed tail-transfer proof.
Neither \(v_L\in D(H^2)\) nor a fourth weak derivative is used.

By the elementary squared-sum bound,
\[
 {1\over2}|(\nabla g_L)\psi|^2
 \le|\nabla f_L|^2|v_L|^2
                              +e^{2f_L}|\nabla\chi|^2|\psi|^2.
\]
The second term is supported in \(R_0<\rho<R_0+1\) and has
integral at most \(4e^{2\alpha(R_0+1)}U^2\), independently of \(L\).
Combining (C1)–(C4) and \(\alpha^2=\delta_0/2\) yields
\[
 \|v_L\|_2^2
 \le {8\over\delta_0}e^{2\alpha(R_0+1)}U^2.                    \tag{C5}
\]
Monotone convergence (or Fatou) gives the same bound for
\(e^{\alpha\rho}\chi\psi\). On \(\rho\ge R_0+1\) this is the
full weighted eigenfunction. On the remaining radii its unweighted
L2 norm is at most \(U\). These two regions give the first estimate
in (C2) with exactly the displayed \(C_\rho\).
The comparison \(S\le\sqrt N\,\rho\) gives the second one.

## 3. Full H2 tails with the same physical exponential rate

The reviewed tail-transfer proof established the local estimate
\[
 \|\psi\|_{H^2_*(\rho>t)}
             \le D\|\psi\|_{L^2(\rho>t-2)}\quad(t\ge3),         \tag{C6}
\]
with
\[
 \begin{split}
 J&=N(N-1)/2,\quad K=2Z\sqrt N+\sqrt{NJ},\\
 G&=2\sqrt{|E|+4NZ^2+2},\\
 B&=6|E|+6K^2+3/2,\\
 D&=6\{|E|+2G+(3N+14)/2\}+6K^2+3/2 .
 \end{split}
\]
Apply (C6) directly to the radial estimate in (C2), before converting
to \(S\). For \(R\ge3\sqrt N\),
\[
 \|\psi\|_{H^2_*(S>R)}
 \le DC_\rho e^{2\alpha}e^{-\alpha R/\sqrt N}.
\]
For \(1\le R\le3\sqrt N\), the global graph bound gives
\(\|\psi\|_{H^2_*}\le BU\). Therefore
\[
 \boxed{\ 
 \|\psi\|_{H^2_*(S>R)}
 \le\max(DC_\rho e^{2\alpha},BUe^{3\alpha})\,
                         e^{-\alpha R/\sqrt N}\quad(R\ge1).\ } \tag{C7}
\]
This avoids introducing a second factor \(1/\sqrt N\) by prematurely
converting the L2 tail to the physical sum coordinate. The gradient
and full ordered Hessian norms, with spin summation, are exactly those
of G3 when \(N=2\).

## 4. How a rank-one hydrogenic comparison supplies (C1)

This section is an explicit implication from an actual comparison
theorem, not a proof of the hydrogen spectrum. Work first in the scalar
two-electron Hilbert space. The same argument applies in the full
fermionic spin-space if its rank-one comparison uses the unit singlet
ground vector. It does not apply a rank-one assertion to unrestricted
spin space, where the unperturbed ground eigenspace has spin multiplicity.

Let \(Z\ge2\), and define the actual normalized hydrogenic functions
\[
 \varphi_Z(x)=(Z^3/\pi)^{1/2}e^{-Z|x|},\qquad
 g_Z(x_1,x_2)=\varphi_Z(x_1)\varphi_Z(x_2),\qquad
 \beta=-5Z^2/8 .
\]
Assume that the actual comparison has been proved on every H2 input:
\[
 \langle Hv,v\rangle
 \ge\beta\|v\|_2^2-{3Z^2\over8}|\langle g_Z,v\rangle|^2.        \tag{C8}
\]
For the singlet version replace \(g_Z\) by its unit-spin lift.
One concrete route to (C8) is:

* The actual noninteracting hydrogenic operator \(H_0\) has
  \(H_0g_Z=-Z^2g_Z\), and its form on the actual domain complement
  of \(g_Z\) is bounded below by \(\beta\).
* The repulsive interaction gives
  \(\langle Hv,v\rangle\ge\langle H_0v,v\rangle\).
* Decompose \(v=\langle g_Z,v\rangle g_Z+w\) inside the actual
  domain. Symmetry and the actual eigenvector equation remove
  the cross term and give (C8).

The complement statement in the first item concerns all vectors
orthogonal to the hydrogenic product, including discrete excitations.
Its value \(-5Z^2/8\) is a hydrogenic discrete-level comparison.
An ionization threshold alone would not justify it.

Suppose also that the actual eigenvalue under study satisfies the
same-charge product trial bound
\[
 E\le E_{\rm trial}:=-Z^2+5Z/8.                                \tag{C9}
\]
This is the expectation of the actual product trial once its Coulomb
integral is proved. The present proof uses (C9) as an explicit bound;
it does not infer that an arbitrary excited eigenvalue satisfies it.
Existence of an eigenfunction below the comparison level requires
its own spectral argument.

If \(v=0\) on \(\rho\le R_0\), Cauchy-Schwarz localizes the rank-one
defect:
\[
 |\langle g_Z,v\rangle|^2
            \le\|g_Z\|_{L^2(\rho>R_0)}^2\|v\|_2^2.            \tag{C10}
\]
The remaining task is a bound on a completely explicit trial function,
not on the unknown physical eigenfunction.

## 5. Exact trial tail and a universal two-electron exterior radius

The normalized radial density of \(|\varphi_Z|^2\) is
\(4Z^3r^2e^{-2Zr}\). Convolving the two radial densities gives
the density of \(S=r+s\) under \(|g_Z|^2\):
\[
 { (2Z)^6\over5!}\,S^5e^{-2ZS}.
\]
Indeed
\(\int_0^S r^2(S-r)^2\,dr=S^5/30\); multiplication by \(16Z^6\)
gives exactly the coefficient above. Five integrations by parts give
\[
 \|g_Z\|_{L^2(S>R)}^2
        =e^{-2ZR}\sum_{k=0}^5{(2ZR)^k\over k!}.                \tag{C11}
\]
Since \(\rho\le S\), the same right side bounds the radial tail.

Choose
\[
 R_0={5\over Z},\qquad
 \delta_0={Z(3Z-5)\over16}>0.                                 \tag{C12}
\]
At \(2ZR_0=10\),
\[
 \sum_{k=0}^5{10^k\over k!}={4433\over3},\qquad
 e^{10}>\sum_{k=0}^{13}{10^k\over k!}
           ={4631613323\over243243}>17732
           =12\cdot{4433\over3}.
\]
Thus (C11) is strictly less than \(1/12\). This is an exact positive
Taylor-series comparison; no reference energy digit or floating-point
exponential value is used.

Using (C8)–(C10) and this tail bound gives
\[
 \begin{split}
 \langle Hv,v\rangle-E\|v\|_2^2
 &\ge\left(\beta-E_{\rm trial}-{Z^2\over32}\right)\|v\|_2^2\\
 &= {Z(11Z-20)\over32}\|v\|_2^2
 \ge {Z(3Z-5)\over16}\|v\|_2^2 .
 \end{split}                                                   \tag{C13}
\]
The last difference is \(5Z(Z-2)/32\ge0\).
This is exactly (C1), on the actual H2 domain, with the constants
in (C12). In particular \(Z=2\) gives \(R_0=5/2\),
\(\delta_0=1/8\), \(\alpha=1/4\). The physical \(S\)-tail exponent
in (C2) and (C7) is then \(1/(4\sqrt2)\).
These deliberately coarse constants are proved, not fitted.

## 6. What this closes and what remains

Once the actual hydrogenic complement comparison and the appropriate
physical eigenpair below (C9) are supplied, this theorem proves
actual exponential L2 and full H2 tails with explicit constants.
The eigenfunction tail is then no longer an independent hypothesis
in the actual-eigenfunction approximation theorem.

The hydrogenic eigenfunction/domain proof, its complement lower bound,
the actual product trial integral, spectral attainment, and the scalar
ground-state symmetry/fermionic comparison remain separate dependencies.
Nothing in this proof substitutes an ionization threshold for the
complement statement. The general exterior theorem itself requires
only (C1), and can be used with other correctly proved exterior bounds.

New paper dependency:
COULOMB_H2_TAIL_TRANSFER_v1.md, SHA-256
c518ebc59a4ad2d533bbc7d967bac1e1d536787f4312960294dd079640ceeaf6.
The exact actual-state downstream theorem is
ACTUAL_EIGENFUNCTION_RWA_AND_APPROXIMATION_v1.md, SHA-256
40b9492a1e7c3f8d6e82a85dad977135cc03b6b89cd320f152e81367b12de696.

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Frozen tag: theorem-t-proof-freeze-2026-09-09.
The frozen tail target is rwa_proof/GLOBAL_DYADIC_ATTEMPT.md,
SHA-256 b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
The bounded exponential-weight argument is classical; no novelty
is claimed for the mechanism. The displayed version is proved
directly, so no inaccessible decay theorem is a logical premise.
Separate independent review is required. No frozen or sealed
successful artifact was modified and no Lean verification is claimed.
