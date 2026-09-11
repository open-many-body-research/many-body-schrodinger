> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Conditional quadratic-weight remainder lemma, version 1

Date: 2026-09-09. Status: **CONDITIONAL PAPER DERIVATION; NOT LEAN VERIFIED; NOVELTY UNASSESSED.** This candidate strengthens a regularity consequence while retaining the actual two-electron Coulomb Hamiltonian and extracted remainder. It neither replaces missing analytic premises with axioms nor proves the full approximation or energy algorithm. The precise premises below must be discharged in any final formal theorem.

## Frozen dependencies and provenance

The following paths are relative to the immutable `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`:

| Path | Frozen SHA-256 |
| --- | --- |
| `dyadic_proof/PHYSICAL_REGULARITY_AUDIT.md` | `972a205569ba54152544e4883754de03130fc98f5c4047277dceed523f98f5b7` |
| `rwa_proof/REMAINDER_EQUATION.md` | `72d59e1c8de1a54313524005caaf6c064999b7747a60563ea5d3396fc7a392a7` |
| `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md` | `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c` |
| `rwa_proof/RWA_THEOREM.md` | `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09` |

No frozen file is modified. The source compatibility review is in `ANALYTIC_AUDIT_v1.md`. The required local C1,1 factorization is a published finite-order theorem, not a full Fock-series identification theorem. [Fournais et al., Theorem 1.1](https://arxiv.org/pdf/math-ph/0312060). The KS descent is an isolated-pair statement; it cannot be invoked at additional simultaneous collisions. [Fournais et al., Proposition 4.4](https://arxiv.org/pdf/0806.1004).

## Precise hypotheses and conclusion

Fix electron count `N=2`, integer `Z>=2`, and a real eigenfunction `psi` of

\[
H_Z=-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u,
\qquad D(H_Z)=H^2(\mathbb R^6),
\]

which is invariant under simultaneous spatial rotations and exchange. Set

\[
S=r+s,\quad T=r^2+s^2,\quad q=x_1\cdot x_2,
\quad f=-ZS+u/2,\quad \psi_0=\psi(0),
\]
\[
\kappa=\frac{Z(2-\pi)}{3\pi},\qquad
R=e^{-f}\psi-\kappa\psi_0q\log T.
\]

The derivation assumes the following mathematical statements, with their actual physical meanings:

1. The distributional eigenfunction and its pointwise representative are compatible with the stated H2 domain. The extracted `R` belongs to Cartesian C1,1 on a fixed neighborhood of the origin, with `R(0)=psi0`. Its rotation invariance implies `DR(0)=0`. Thus `|R(x)−psi0|<=C|x|²` there.
2. The distributional scaled conjugated equation (PDE10)–(PDE12) is valid, and the isolated-pair KS pullback of an H2 solution of the associated inhomogeneous physical equation is valid in distributions.
3. On every fixed normalized isolated-pair chart, the uniform analytic operator lemma (U1) holds for `P_c+B_epsilon`, `c=4` or `1`, with a common L2 bound for the unknown, common factorial source bounds, and potential analytic norm `O(epsilon)`. On the collision-free charts the corresponding uniform elliptic estimate holds.
4. Common analytic bounds of an actual KS pullback descend quantitatively to analytic-plus-distance form. Rotation invariance and the nonvertex distance-coordinate chart cover preserve a common analytic radius and amplitude, as detailed in frozen RWA §5. The normalized shell has only isolated pair collisions; this is special to two electrons.

Under these hypotheses, there exist `delta,C,A>0`, independent of the derivative order and of the point, such that the reduced remainder obeys

\[
\boxed{\quad
|\partial^\nu(\widehat R-\psi_0)(a,b,c)|
\le CA^{|\nu|}\nu! S^{2-|\nu|},\qquad
0<S=a+b+2c<\delta.
\quad} \tag{QW1}
\]

The statement includes compatible analytic-germ derivatives at every nonvertex boundary stratum of the closed perimetric octant. No sign, simplicity, or nonzero value of `psi0` is required for this implication. Applying it to a ground state additionally requires proving that the ground state satisfies the stated hypotheses.

## 1. Preserve the quadratic amplitude

Let `X=(X1,X2)` range over a fixed slightly enlarged normalized shell containing `1/2<=S(X)<=2`, and take `0<epsilon<=epsilon0` so that `epsilon X` remains in the C1,1 neighborhood. Define

\[
V_\varepsilon(X)=\frac{R(\varepsilon X)-\psi_0}{\varepsilon^2},
\qquad
h_\varepsilon(X)=e^{\varepsilon f(X)}V_\varepsilon(X).
\]

Hypothesis 1 makes `V_epsilon` and `h_epsilon` uniformly bounded on this real shell. Their KS pullbacks therefore have uniformly bounded L2 norms on fixed finite-volume lifted charts. This estimate does not use any all-order regularity, nor any norm equivalence through the singular KS Jacobian.

Write all quantities below at normalized `X`, and introduce

\[
\Theta=\frac{S(rs-q)}{2rsu},\quad
W=-Z^2-\tfrac14-E+Z\Theta,\quad
C_1=-\frac{ZqS}{rs}-\frac u2,\quad
L_\varepsilon=2\log\varepsilon+\log T.
\]

The displayed expression for `Theta` equals the frozen one: `ab=(rs−q)/2`, since `q=(r²+s²−u²)/2`. Dividing (PDE12) by `epsilon²` gives the exact equation

\[
\mathcal P_\varepsilon V_\varepsilon
=\psi_0\left\{\kappa\left[
(8+2\varepsilon f)\frac qT
+(\varepsilon C_1-\varepsilon^2Wq)L_\varepsilon
\right]-W\right\}, \tag{QW2}
\]

where

\[
\mathcal P_\varepsilon=
e^{-\varepsilon f}
\left(-\tfrac12\Delta+\varepsilon V_{\rm Coul}
-\varepsilon^2E\right)e^{\varepsilon f}.
\]

Some coefficients on the right of (QW2) are **not** analytic in ordinary perimetric variables at a pair axis. The next calculation, rather than an analyticity assertion about (QW2), is what permits the uniform lemma.

## 2. Full cleared nuclear source

On the nuclear chart, take `X1=K(y)`, `X2=t`, `d=|y|²`; use the same notation for the polynomial `d=sum y_i²` in complex variables. Here

\[
r=d,\quad s=\sqrt{t\cdot t},\quad
u=\sqrt{(K(y)-t)\cdot(K(y)-t)},\quad
q=K(y)\cdot t.
\]

The two square-root branches are chosen from their positive real values on a chart where `s,u>=d0>0`. They extend to one common complex neighborhood. `S=d+s`, `T=d²+s²`, and `f=−Z(d+s)+u/2` are analytic there, with `T` uniformly separated from zero.

Define the explicitly analytic cleared quantities

\[
\begin{aligned}
\Omega_{\rm nuc}=dW
&=d(-Z^2-\tfrac14-E)
+\frac{ZS(ds-q)}{2su},\\
\Gamma_{\rm nuc}=dC_1
&=-\frac{ZqS}{s}-\frac{du}{2}.
\end{aligned} \tag{QW3}
\]

All denominators in (QW3) are separated spectator distances. There is no surviving division by `d` or `r`. Let `v_epsilon=h_epsilon(K(y),t)` and let `Q_epsilon` be the nuclear KS operator (R3), whose principal part is `−Delta_y−4d Delta_t`. Exact conjugation followed by multiplication by `8d` gives

\[
\boxed{
Q_\varepsilon v_\varepsilon
=8\psi_0e^{\varepsilon f}\left\{
\kappa\left[(8+2\varepsilon f)\frac{dq}{T}
+(\varepsilon\Gamma_{\rm nuc}
-\varepsilon^2\Omega_{\rm nuc}q)L_\varepsilon\right]
-\Omega_{\rm nuc}\right\}.
} \tag{QW4}
\]

This formula records every scale factor, the constant-subtraction term, and every logarithmic contribution. The analogous second nuclear chart follows by electron exchange.

## 3. Full cleared electron-pair source

On the electron-pair chart, take `X=X1−X2=K(y)`, `t=(X1+X2)/2`, `d=|y|²`. Then

\[
u=d,\quad r=\sqrt{(t+K(y)/2)\cdot(t+K(y)/2)},\quad
s=\sqrt{(t-K(y)/2)\cdot(t-K(y)/2)},
\]
\[
q=t\cdot t-\tfrac14d^2,\qquad
S=r+s,\quad T=r^2+s^2.
\]

Here `r,s>=d0>0` are separated, so their branches and reciprocal functions are uniformly analytic. Set

\[
\begin{aligned}
\Omega_{\rm ee}=dW
&=d(-Z^2-\tfrac14-E)+\frac{ZS(rs-q)}{2rs},\\
\Gamma_{\rm ee}=dC_1
&=-\frac{ZdqS}{rs}-\frac{d^2}{2}.
\end{aligned} \tag{QW5}
\]

There is no surviving division by `d` or `u`. For the corresponding pullback `v_epsilon`, the electron-pair KS operator is (R5), with principal part `−Delta_y−d Delta_t`. The exact equation is

\[
\boxed{
Q_\varepsilon v_\varepsilon
=4\psi_0e^{\varepsilon f}\left\{
\kappa\left[(8+2\varepsilon f)\frac{dq}{T}
+(\varepsilon\Gamma_{\rm ee}
-\varepsilon^2\Omega_{\rm ee}q)L_\varepsilon\right]
-\Omega_{\rm ee}\right\}.
} \tag{QW6}
\]

The difference between factors eight and four is essential and follows from the physical relative-coordinate kinetic energy.

## 4. Common source norms and descent

Choose the complex neighborhoods once, at normalized scale, with all indicated square roots and `log T` analytic and bounded. All fixed factors in (QW4) and (QW6) then have a common holomorphic bound. The only unbounded real parameter, `log epsilon`, occurs multiplied by `epsilon` or `epsilon²`:

\[
\sup_{0<\varepsilon\le1}\varepsilon|\log\varepsilon|=1/e,
\qquad
\sup_{0<\varepsilon\le1}\varepsilon^2|\log\varepsilon|=1/(2e).
\]

Thus these right-hand sides have common holomorphic norms and, by Cauchy, common factorial derivative bounds. The unknown has the independent uniform real L2 bound from §1. The potentials in the two `Q_epsilon` are still the same `O(epsilon)` analytic potentials as in the frozen uniform lemma. Hypothesis 3 therefore yields common factorial bounds for each `v_epsilon` on smaller fixed lifted charts.

On the collision-free part of the compact normalized shell, every denominator in (QW2) is separated. Multiplication by `e^(epsilon f)` converts it back to the original uniformly elliptic Cartesian equation for `h_epsilon`, with the same bounded logarithmic factors. The elliptic clause of Hypothesis 3 supplies common analytic bounds there.

Apply Hypothesis 4 to the rotation-invariant physical function `h_epsilon`. Its actual KS pullbacks satisfy the fiber condition. Quantitative descent gives common analytic coefficients, and invariant distance-coordinate conversion gives common holomorphic perimetric neighborhoods of the normalized shell. Multiplication by `e^(−epsilon f)`, which is an ordinary distance-analytic multiplier of common norm, recovers common holomorphic bounds for `V_epsilon`. The chart cores and retained radii can be chosen before `epsilon`, so their finite minimum is positive and independent of it. This proves a common radius `r*>0` and bound `M*>0` for `V_epsilon` near every normalized point with `S=1`.

## 5. Return to physical scale

Fix any requested point `x=(a,b,c)`, let `epsilon=S(x)`, and let `z0=x/epsilon`. While differentiating the local extension, hold `epsilon` fixed. Cauchy's estimate gives

\[
\left|\partial_z^\nu
\bigl[\widehat R(\varepsilon z)-\psi_0\bigr]_{z=z_0}\right|
\le M_*\varepsilon^2(2/r_*)^{|\nu|}\nu!.
\]

The chain rule gives (QW1), with `A=max(1,2/r*)`. No derivative of the pointwise scale selection is introduced. Boundary derivatives are those of the compatible local germs.

## Scope

The implication proves that, **if** the listed actual finite-order, weak-equation, uniform analytic and descent premises hold, the quadratic spatial weight is retained at all orders. It improves the frozen linear-weight consequence without altering the remainder or Hamiltonian. It does not show the exponent two is optimal, establish an effective value for its constants, identify an infinite Fock expansion, prove a new global dictionary rate, or produce an executable algorithm. No numerical or Lean test was performed for this candidate.

For `N=3`, the normalized shell contains additional simultaneous collisions, such as `x1=x2=0` with `x3!=0`. The separated-denominator calculations in §2 would then fail. This derivation therefore supplies no three-electron generalization by itself.
