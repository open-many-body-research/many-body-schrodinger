> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Global Poisson-shell construction in the exact dyadic dictionary

This is a conditional paper proof. Its three physical inputs are stated precisely below. In particular, the exterior analytic input is the statement of [EXTERIOR_ANALYTIC_ATTEMPT.md](EXTERIOR_ANALYTIC_ATTEMPT.md); the present file does not independently prove it. Once those inputs have passed their separate audits, this argument supplies the global approximation and normalized graph RATE. No numerical experiment, added basis element, or Lean verification is asserted here.

**Completed physical application — PROVEN (paper).** All three inputs have now been discharged: G1 follows from the stronger pre-extraction bound (R11)–(R14) in [RWA_THEOREM.md](RWA_THEOREM.md); G2 is proved in the exterior theorem, including its corrected projected-center bound and [independent audit](EXTERIOR_ANALYTIC_AUDIT.md); G3 is the preserved [physical tail theorem](../dyadic_proof/EXTERIOR_CONSTANTS.md). The full construction below passed [GLOBAL_DYADIC_AUDIT.md](GLOBAL_DYADIC_AUDIT.md). Therefore G4 and G27 apply to the actual fixed-charge atom without an open physical approximation premise. The conditional formulation below separates the construction from the proofs of its inputs.

## 1. The precise physical inputs

Fix \(Z\ge2\). Let \(\psi\) be the normalized positive atomic two-electron ground state, invariant under rotations and electron exchange. Put \(\psi_0=\psi(0)\), \(f=\widehat\psi-\psi_0\), and \(S=a+b+2c\). Assume:

**G1 — vertex factorial estimate.** For some \(C_v,A_v,\delta_v>0\) and \(0<\sigma<1\),
\[
|\partial^\nu f(x)|\le C_vA_v^{|\nu|}|\nu|!S(x)^{\sigma-|\nu|}
\quad(0<S(x)<\delta_v),
\tag{G1}
\]
with compatible nonvertex boundary analytic extensions. RWA for the extracted remainder, together with the already-verified leading-log term and analytic cusp multiplier, implies this estimate. Alternatively the stronger direct vertex estimate for \(\widehat\psi-\psi_0\) supplies it. No full Fock expansion is needed.

**G2 — exterior distance analyticity.** For each fixed \(d>0\), there are \(c_d,M_d>0\) such that every closed-octant point \(x\) with \(S(x)\ge d\) has a compatible holomorphic extension to
\[
\{z:|z-x|_\infty<c_d/(1+S(x))\},
\]
bounded by \(M_d\). Only one fixed \(d<\delta_v/8\) is needed in this proof.

**G3 — physical tail and domain.** \(\psi\in H^2(\mathbb R^6)\), and for constants \(C_t,\gamma>0\),
\[
\|\psi\|_{H^2_*(\{S>R\})}\le C_te^{-\gamma R}
\quad(R\ge1).
\tag{G3}
\]
The previously proved physical \(\rho\)-tail gives this with \(\gamma=Z/(4\sqrt2)\), after enlarging \(C_t\) on a fixed bounded interval. Replacing \(C_t\) by \(\max(C_t,e^\gamma\|\psi\|_{H^2_*})\) extends the same bound to all \(R\ge0\); that extension is used below.

All constants in this file may depend on these fixed inputs and on \(Z\). They do not depend on the dictionary index or on a shrinking/growing shell.

**Conditional conclusion.** There exist \(C,c>0\) and \(v_n\in V_n^{(Z)}\) such that
\[
\|\psi-v_n\|_{H^2_*(\mathbb R^6)}\le Ce^{-cn^{1/16}}.
\tag{G4}
\]
After normalization this gives the genuine ground-state graph residual RATE in the unchanged dictionary.

## 2. A global finite-order envelope

The three estimates with \(|\nu|\le2\) in (G1), together with Cauchy's inequalities from G2 on \(S\ge d\), give one constant \(C_g\) with
\[
|\partial^\nu f(x)|\le C_g S^{\sigma-|\nu|}(1+S)^4,
\qquad |\nu|\le2,\ S>0.
\tag{G5}
\]
To check the exponent four, exterior Cauchy bounds cost at most \((1+S)^i\) at derivative order \(i\le2\); for large \(S\), the right side of (G5) has exponent \(4+\sigma-i\ge i\). The compact interval between the vertex region and \(S=1\) is absorbed into \(C_g\). The zero-order estimate uses the bounded amplitude in G2 and the fixed number \(\psi_0\). This step uses only two exterior derivative orders, not a false global version of the vertex weight.

## 3. Polynomial shell approximation with explicit outer-scale dependence

Use the fixed normalized shell
\[
K=\{y\ge0:1/4\le S(y)\le2\}.
\]
For every \(T\ge1\) and every \(0<\tau\le T\), let
\[
F_\tau(y)=\tau^{-\sigma}f(\tau y).
\]
There are constants \(c_h,M_h>0\), independent of \(T,\tau\), such that these functions have compatible holomorphic extensions near \(K\) with common radius
\[
h_T=c_h(1+T)^{-2},\qquad \|F_\tau\|_{\mathrm{hol}}\le M_h.
\tag{G6}
\]
For small \(\tau\), (G1) and the convergent Taylor series prove (G6) with a fixed radius and amplitude. For scales bounded away from zero, G2 rescales its radius to at least \(c/[\tau(1+2\tau)]\); \(\tau^{-\sigma}\) is then bounded. Enlarging the fixed intermediate-scale constants covers the overlap. The radius can be decreased to have \(0<h_T\le1/100\).

The constructive Gevrey-cutoff and Chebyshev argument in [DYADIC_REMAINDER_ATTEMPT.md](DYADIC_REMAINDER_ATTEMPT.md), section 1, now yields symmetric ordinary polynomials \(Q_{\tau,q}\), degree at most \(q\), satisfying
\[
\max_{|\nu|\le2}\sup_K
|\partial^\nu(F_\tau-Q_{\tau,q})|
\le C(1+T)^{62}
\exp\left[-\frac{b\sqrt q}{(1+T)^4}\right].
\tag{G7}
\]
On the nonnegative cone, with \(t=S(y)\), they also satisfy
\[
\begin{array}{ll}
|\partial^\nu Q_{\tau,q}(y)|\le C(1+T)^{62},&0\le t\le2,\\[1mm]
|\partial^\nu Q_{\tau,q}(y)|
\le C(1+T)^{62}(q+1)^4(6t)^q,&t\ge2,
\end{array}
\quad |\nu|\le2.
\tag{G8}
\]

Here is the conservative constant accounting; no bounded-overlap improvement is required. A fixed-dimensional grid of mesh proportional to \(h_T\) needs at most \(N_T=C h_T^{-3}\) boxes. Each Gevrey-2 cutoff takes values in \([0,1]\) and has derivative bound \((C/h_T)^k(k!)^2\). The telescoping product weights contain at most \(N_T\) such factors. Leibniz's formula bounds their derivatives by
\[
(C N_T/h_T)^k(k!)^2.
\]
There is no constant raised to \(N_T\) at order zero: every undifferentiated cutoff is at most one. Multiplication by a single analytic coefficient and summation over the boxes therefore give an extension on a fixed cube with
\[
\|\partial^\nu G_\tau\|_\infty
\le M_0B_0^{|\nu|}(|\nu|!)^2,
\quad M_0\le C h_T^{-3},\quad B_0\le C h_T^{-4}.
\tag{G9}
\]
Composition with cosines on the fixed containing cube changes only the absolute constants. The Fourier coefficient argument then has decay parameter at least \(b_0h_T^2\). The count of frequency triples and the two derivative losses give the sum
\[
\sum_{N>d}(N+1)^6e^{-b_0h_T^2\sqrt N}
\le C h_T^{-28}e^{-b_0h_T^2\sqrt d/2}.
\]
Indeed reserve half the exponential for the tail factor, compare the remainder with an integral, and substitute \(t=\sqrt N\); the resulting moment has degree thirteen and contributes the fourteenth inverse power of \(b_0h_T^2\). Multiplying by \(M_0\) gives \(h_T^{-31}=C(1+T)^{62}\). Taking tensor degree \(d=\lfloor q/3\rfloor\) proves (G7) and the absolute coefficient-sum bound needed in (G8). Thus neither a cover size nor a Gevrey constant has an exponential dependence on \(T\).

## 4. One global admissible witness and its exact error identity

For an integer \(q\ge1\), set
\[
p=J=256(q+1),\qquad T=(q+1)^{1/16},\qquad a_j=Z2^j,\qquad \tau_j=p/a_j.
\tag{G10}
\]
For all sufficiently large \(q\), let \(j_0\) be the least nonnegative integer with \(a_{j_0}\ge p/T\). Explicit sufficient conditions are
\[
p/T>Z,\qquad 2^J\ge2p/(ZT).
\]
They ensure
\[
j_0\le J,\qquad T/2<\tau_{j_0}\le T.
\tag{G11}
\]
Write \(E_p(z)=e^{-z}\sum_{l=0}^p z^l/l!\), and
\[
W_{j,p}(S)=E_p(a_jS)-E_p(a_{j+1}S),\qquad
P_j(x)=\tau_j^\sigma Q_{\tau_j,q}(x/\tau_j).
\]
Define the single global function
\[
v_q=\psi_0 E_p(a_{j_0}S)+\sum_{j=j_0}^J W_{j,p}(S)P_j(x).
\tag{G12}
\]
The constant part uses the **same outer node** as the telescoping shell sum. This choice is essential. Put \(E_{\mathrm{out}}=E_p(a_{j_0}S)\) and \(E_{\mathrm{in}}=E_p(a_{J+1}S)\). Exact telescoping gives
\[
\boxed{\quad
\psi-v_q=
\psi(1-E_{\mathrm{out}})+fE_{\mathrm{in}}
+\sum_{j=j_0}^J W_{j,p}(f-P_j).
\quad}
\tag{G13}
\]
In particular the outer omitted target is \(\psi\), which has a physical tail, rather than the nondecaying function \(f=\psi-\psi_0\). This identity cancels the false constant exterior bulk present in a purely local construction.

Every summand has the prescribed node and ordinary polynomial degree at most \(p+q\), including the adjacent node \(j+1\). Hence
\[
v_q\in V_{p+q+2(J+1)}^{(Z)}
=V_{769q+770}^{(Z)}.
\tag{G14}
\]
This also proves global domain membership: a distance polynomial times a decaying exponential belongs to physical \(H^2\); inverse-distance Hessian terms are square integrable. Electron exchange symmetry is preserved. No intermediate cutoff is part of (G12).

## 5. Global shell error, including each polynomial's exterior

The scalar Poisson estimates (D9)–(D10) and physical norm conversion (D11)–(D12) in the local proof apply on all of \(\mathbb R^6\). Put
\[
M_T=C(1+T)^{62},\qquad
\epsilon_{T,q}=M_T\exp[-b\sqrt q/(1+T)^4].
\]
On the fitted shell \(1/4\le S/\tau_j\le2\), the norm estimate is
\[
\|W_{j,p}(f-P_j)\|_{H^2_*,\mathrm{fit}}
\le C(p+1)^3\tau_j^{\sigma+1}(1+\tau_j^2)\epsilon_{T,q}.
\tag{G15}
\]
The extra \(1+\tau_j^2\) retains the zero-order and first-order physical norm scales when the shell radius exceeds one. Omitting it would be incorrect on growing outer shells.

For \(t=S/\tau_j\le1/4\), the estimate
\[
e^{-pI(2t)}\le e^{-p/8}(4t)^{p/2}
\]
absorbs all inverse powers arising from derivatives of \(f\), the weight, or the physical distance Hessians. The global envelope (G5) contributes at most \((1+T)^4\) on this portion of the shell, which is bounded by \(C M_T\). The bounded-cube polynomial estimates are (G8). The resulting lower-tail norm is bounded by
\[
C(p+1)^3(q+1)^4M_T\tau_j^{\sigma+1}(1+\tau_j^2)e^{-p/16}.
\]

For \(t\ge2\), (G5) gives factors bounded by
\(C\tau_j^{\sigma-i}(1+T)^4t^{\sigma-i}(1+t)^4\) at derivative order \(i\le2\). Combining with the Poisson derivatives and (G8), an upper envelope for the squared physical integral is a fixed prefactor times
\[
12^{2q}e^{-p/2}\int_2^\infty
t^{21}(t/2)^{2q-2p}\,dt.
\tag{G16}
\]
The exponent twenty-one is a deliberately larger bound than needed: it includes the six-dimensional volume, two derivatives, the factor \((1+S)^4\) in (G5), and the polynomial growth of the window derivatives. The integral equals
\[
\frac{2^{22}}{2p-2q-22}
\qquad(p>q+11).
\]
Since \(\log12<3\) and \(p=256(q+1)\), its square root times the exponential prefactor is at most \(C e^{-p/16}\). Thus all three regions give
\[
\begin{aligned}
\|W_{j,p}(f-P_j)\|_{H^2_*}
\le C(p+1)^3(q+1)^4M_T\tau_j^{\sigma+1}(1+\tau_j^2)
\left[e^{-b\sqrt q/(1+T)^4}+e^{-p/16}\right].
\end{aligned}
\tag{G17}
\]
These estimates directly control the exterior of **the same polynomials used in the witness**. They are not estimates merely for a compactly supported shell surrogate.

The geometric sum satisfies
\[
\sum_{j=j_0}^J\tau_j^{\sigma+1}(1+\tau_j^2)
\le C_\sigma\{T^{\sigma+1}+T^{\sigma+3}\}
\le C_\sigma(1+T)^4.
\tag{G18}
\]
Consequently the total shell error is at most
\[
C(p+1)^3(q+1)^4(1+T)^{66}
\left[e^{-b\sqrt q/(1+T)^4}+e^{-p/16}\right].
\tag{G19}
\]

## 6. Inner omission

Let \(\tau_* = p/(Z2^{J+1})\). For sufficiently large \(q\), \(2\tau_*<\delta_v\) and \(\tau_*\le1\). On \(S\le2\tau_*\), (G1) and the first two derivatives of \(E_p\) show
\[
\|fE_{\mathrm{in}}\|_{H^2_*(S\le2\tau_*)}
\le C(p+1)^3\tau_*^{\sigma+1}.
\]
On \(S\ge2\tau_*\), use (G5) and \(1+\tau_*t\le1+t\). For \(t\ge2\), the gamma density representation gives
\[
E_p(pt)\le2e^{-pI(t)},
\]
because the logarithmic derivative of the density on \([pt,\infty)\) is at most \(-1/2\). Its first two derivatives obey the same bound with polynomial factors in \(p,t\). The integral calculation from (G16), with no growing polynomial degree needed, is then finite with a uniform constant. Hence
\[
\|fE_{\mathrm{in}}\|_{H^2_*}
\le C(p+1)^3\left[\frac{p}{Z2^{J+1}}\right]^{\sigma+1}.
\tag{G20}
\]
The subtraction of \(\psi_0\) is what gives this small inner error. An omitted constant would have a different scaling.

## 7. Outer omission: physical tail and localized Hardy

Write \(\tau_0=\tau_{j_0}\in(T/2,T]\) and \(g(S)=1-E_p(pS/\tau_0)\).

On \(S<T/8\), one has \(t=S/\tau_0<1/4\). The gamma upper-tail estimate and its first two derivatives give
\[
\sup_{0<S<T/8}|g^{(i)}(S)|
\le C(p+1)^3\tau_0^{-i}e^{-p/16},
\qquad i=0,1,2.
\tag{G21}
\]
To remove the apparent \(t^{-i}\) at zero in these formulas, use the remaining factor \((4t)^{p/2}\) in (D10); its supremum after multiplication by \(t^{-i}\) is finite for \(p\ge256\).

Since \(|\nabla S|=\sqrt2\) and \(\|D^2S\|_F\le\sqrt2(1/r+1/s)\), the product rule and global sliced Hardy estimates give
\[
\|g\psi\|_{H^2_*(S<T/8)}
\le C(p+1)^3(1+\tau_0^{-2})e^{-p/16}\|\psi\|_{H^2_*}.
\tag{G22}
\]
For example \(\|\psi/r\|_2\le2\|\nabla_{x_1}\psi\|_2\); restricting the integral to this region only decreases the left side. No derivative of a sharp region indicator is taken.

On \(S\ge T/8\), no small scalar multiplier is required. Globally \(|g|\le1\), and from the gamma density formula
\[
|g'|\le p/\tau_0,\qquad |g''|\le2p^2/\tau_0^2.
\]
To localize the inverse-distance term in the Hessian product rule, take a Lipschitz cutoff \(\chi\) equal to zero on \(S\le T/16\), one on \(S\ge T/8\), and satisfying \(|\nabla\chi|\le C/T\). This cutoff is used only in the Hardy estimate, not in the dictionary. Then
\[
\|\psi/r\|_{L^2(S\ge T/8)}
\le2\|\nabla_{x_1}(\chi\psi)\|_2
\le C(1+T^{-1})\|\psi\|_{H^1(S>T/16)},
\]
and the identical estimate holds for \(s\). Applying the product rule and (G3), for sufficiently large \(T\), proves
\[
\|g\psi\|_{H^2_*(S\ge T/8)}
\le C(p+1)^2(1+T^{-2})e^{-\gamma T/16}.
\tag{G23}
\]
Thus the full outer error is exponentially small in the growing physical radius. The use of Hardy is indispensable: a physical \(H^2\) tail alone does not pointwise bound \(\psi/r\) on this region.

## 8. Global rate and normalized ground residual

Combining (G13), (G19), (G20), (G22), and (G23), and using \(T\ge1\), yields the explicit schedule bound
\[
\begin{aligned}
\|\psi-v_q\|_{H^2_*}\le C(p+1)^3(q+1)^4(1+T)^{66}
\bigg[
&e^{-b\sqrt q/(1+T)^4}+e^{-p/16}\\
&+e^{-\gamma T/16}
+\left(\frac{p}{Z2^{J+1}}\right)^{\sigma+1}\bigg].
\end{aligned}
\tag{G24}
\]
All exponents and polynomial prefactors have been tracked. Since \(T=(q+1)^{1/16}\),
\[
\frac{\sqrt q}{(1+T)^4}\ge c_1q^{1/4}
\]
for \(q\ge1\), whereas the physical tail is \(e^{-c_2q^{1/16}}\). The other terms decay exponentially in \(q\). Every polynomial prefactor in (G24) is absorbed into a smaller positive multiple of \(q^{1/16}\). This proves
\[
\|\psi-v_q\|_{H^2_*}\le C'e^{-c'q^{1/16}}.
\tag{G25}
\]
With the exact index (G14), fill intermediate \(n\) using \(q=\lfloor(n-770)/769\rfloor\), and enlarge \(C'\) over the finitely many excluded small indices. This proves (G4).

For completeness, Coulomb graph control has an explicit sufficient bound
\[
\|(H_Z-E_Z)e\|_2
\le K_Z\|e\|_{H^2_*},\qquad
K_Z=\sqrt6/2+4Z+2+Z^2.
\tag{G26}
\]
The kinetic estimate is \(\|\Delta e\|_2\le\sqrt6\|D^2e\|_2\). Sliced Hardy bounds the two nuclear terms by \(4Z\|\nabla e\|_2\), the electron-electron term by \(2\|\nabla e\|_2\), and \(|E_Z|\le Z^2\) bounds the energy term. This loose constant is sufficient.

For large indices \(\|\psi-v_n\|_2\le1/2\), hence \(\|v_n\|_2\ge1/2\). Define \(\phi_n=v_n/\|v_n\|_2\). Then
\[
\|(H_Z-E_Z)\phi_n\|_2
=\frac{\|(H_Z-E_Z)(v_n-\psi)\|_2}{\|v_n\|_2}
\le2K_ZCe^{-cn^{1/16}}.
\tag{G27}
\]
For finitely many smaller indices use any fixed normalized anchor from the dictionary and enlarge the constant. The graph residual is for the physical ground state and the original continuum operator; it is not merely a variational-energy, finite-basis, or variance convergence statement.

## 9. Audit scope

The construction handles both previous globalization issues: (G12) is one admissible global witness, and (G16), (G20), and (G23) control the actual exterior of that same witness through the exact cancellation identity (G13). It uses the original nodes \(Z2^j\), original degree budget \(n-2j\), and physical six-dimensional \(H^2\) norm throughout.

The remaining dependency of this file is verification of the exact physical inputs G1–G3. In particular, it must not be read as an independent proof of the exterior analytic chart theorem. Conditional regularity-to-RATE composition is mathematically different from establishing those physical regularity inputs. The effective finite-dimensional algorithm and its bit-cost accounting are also separate from this approximation proof.
