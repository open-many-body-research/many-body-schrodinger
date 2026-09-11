> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Exact-dictionary local remainder approximation, conditional on RWA

This file does not prove RWA. Its sole premise concerning the physical remainder is the precise all-order RWA estimate. The construction below proves a local approximation consequence with the original nodes and degree allocation. It is a paper proof; no Lean verification or numerical RATE experiment is asserted.

## Statement

Let \(Z>0\), let \(0<\sigma<1\), and suppose a real function \(f\) on the closed half-perimetric cone is symmetric under \(a\leftrightarrow b\). Write \(S=a+b+2c\). Suppose, for constants \(C_*,A_*,\delta_*>0\),

\[
|\partial^\nu f(a,b,c)|\le C_* A_*^{|\nu|}|\nu|!S^{\sigma-|\nu|}
\quad(0<S<\delta_*),
\tag{D1}
\]

with compatible analytic extensions at nonvertex boundary points. Then there are \(D,C,c>0\), depending only on these constants and \(Z\), and members \(v_n\in V_n^{(Z)}\), such that

\[
\|f-v_n\|_{H^2_*(B_D)}\le C e^{-c\sqrt n}.
\tag{D2}
\]

Here the norm is the physical six-dimensional Cartesian norm, and \(f\) is understood as its rotationally invariant Cartesian lift. Every final witness is a finite sum of the prescribed exponentials times ordinary distance polynomials. Smooth auxiliary cutoffs occur only in the construction of ordinary polynomial coefficients; they do not multiply the final witness.

The same conclusion holds for \(f+f_0\) with any fixed real constant \(f_0\). Consequently, **if RWA is proved**, it applies to the requested physical target

\[
e^{-ZS+u/2}\mathcal R_Z.
\]

Indeed subtracting its value \(\psi_Z(0)\) gives (D1): the product rule and analyticity of the exponential preserve the factorial bound, while \(e^{-ZS+u/2}-1=O(S)\) is admissible because \(\sigma<1\). This inference concerns the local remainder, not the global eigenfunction residual.

## 1. Uniform polynomial approximation on a fixed shell

Use the normalized shell

\[
K=\{(a,b,c)\ge0:1/4\le a+b+2c\le2\}.
\]

For \(0<\tau\le\delta_*/4\), define \(F_\tau(y)=\tau^{-\sigma}f(\tau y)\). On a slightly enlarged shell the derivative bounds from (D1) are uniform in \(\tau\). Taylor's theorem gives analytic extensions to complex balls of a common positive radius, bounded by a common constant: choosing that radius below \(1/(32A_*)\), the multivariate Taylor series is bounded by the convergent sum of \(C(3/4)^k\). Overlapping series agree by uniqueness from the real interior. Compactness of this fixed shell therefore gives a finite collection of analytic boxes, independent of \(\tau\), with uniform bounds.

There are constants \(M,B,b>0\), independent of \(\tau\) and degree \(q\), and symmetric ordinary polynomials \(Q_{\tau,q}\) of degree at most \(q\), such that

\[
\max_{|\nu|\le2}\sup_K
|\partial^\nu(F_\tau-Q_{\tau,q})|
\le M e^{-b\sqrt q},
\tag{D3}
\]

and, writing \(t=S(y)\),

\[
\begin{array}{ll}
|\partial^\nu Q_{\tau,q}(y)|\le M,&0\le t\le2,\\[2mm]
|\partial^\nu Q_{\tau,q}(y)|\le M(q+1)^4(6t)^q,&t\ge2,
\end{array}
\qquad |\nu|\le2.
\tag{D4}
\]

Increasing the common \(M\) handles the finitely many small degrees.

Here is a direct proof rather than an invocation of polynomial approximation on a polytope. The flat function \(h(t)=e^{-1/t}\) for \(t>0\), zero otherwise, obeys

\[
\|h^{(k)}\|_\infty\le9^k(k!)^2.
\]

To see this, use a complex circle of radius \(t/2\): there \(\operatorname{Re}(1/z)\ge2/(9t)\). Cauchy's estimate gives \(k!(2/t)^k e^{-2/(9t)}\); maximize over \(t\), and use \(k!\ge(k/e)^k\). Integrating \(h(t)h(1-t)\) and dividing by its positive integral gives a Gevrey-2 step. Its normalization is bounded using
\(\int h(t)h(1-t)dt\ge e^{-6}/2\). Products and fixed affine rescalings produce a finite box cover with cutoff functions \(\chi_i\) equal to one on inner boxes covering \(K\), and supported strictly inside the corresponding analytic boxes.

Use the weights

\[
\omega_i=\chi_i\prod_{h<i}(1-\chi_h).
\]

Their sum is one on \(K\). The extension
\(G_\tau=\sum_i\omega_iF_{\tau,i}\), where \(F_{\tau,i}\) is the analytic extension in box \(i\), is smooth and compactly supported in a fixed cube \([-B,B]^3\), which may be enlarged to have \(B\ge4\). It equals \(F_\tau\) on a neighborhood of \(K\). Leibniz's formula, \(\prod_jk_j!\le(\sum_jk_j)!\), and the finite number of factors show

\[
\|\partial^\nu G_\tau\|_\infty\le M_0B_0^{|\nu|}(|\nu|!)^2,
\tag{D5}
\]

with \(M_0,B_0\) determined by the fixed cover and the preceding bounds. The flat cutoff makes each product extend by zero across the edge of its analytic box.

Now set \(g_\tau(\theta)=G_\tau(B\cos\theta_1,B\cos\theta_2,B\cos\theta_3)\). For derivatives in one angular variable, the chain rule grouped by ordered compositions gives a bound \(M_1B_1^k(k!)^2\), uniformly in the other variables. For example, dropping the factorial denominators associated with derivatives of cosine bounds the order-\(k\) sum by

\[
M_0 k!\sum_{l=1}^k (B_0B)^l l!\binom{k-1}{l-1}
\le M_0(k!)^2B_0B(1+B_0B)^{k-1}.
\]

Integrating a Fourier coefficient by parts \(k\) times in a largest-frequency direction gives
\(M_1 B_1^k(k!)^2/N^k\), where \(N\) is that frequency. Take \(k=\lfloor\sqrt{N/(4B_1)}\rfloor\). Using \(k!\le k^k\) proves a bound \(M_2e^{-b_0\sqrt N}\). Tensor cosine truncation through degree \(d\) in each variable is a polynomial in \(a,b,c\) of total degree at most \(3d\). The bounds \(\|T_k\|\le1\), \(\|T_k'\|\le k^2\), and \(\|T_k''\|\le k^4\) show absolute convergence through two derivatives; summing the coefficient tail proves (D3) for \(d=\lfloor q/3\rfloor\). The whole derivative series is bounded independently of \(q\) on the cube, giving the first line of (D4). Outside it, the elementary Chebyshev recurrence bounds the same polynomial and its first two derivatives by the second line of (D4), after enlarging \(M\). Symmetrization in \(a,b\) preserves all these bounds.

This argument deliberately pays a square root in the rate. It needs no unverified theorem claiming exponential ordinary-polynomial approximation on an arbitrary analytic polytope.

For explicit growth accounting in (D4), the absolute sum of the Chebyshev coefficients is bounded independently of the truncation degree. For \(i\le2\), the recurrence or the explicit polynomial formula gives
\[
|T_k^{(i)}(x/B)|B^{-i}
\le C(k+1)^{2i}(1+2|x|/B)^k.
\]
On the nonnegative normalized cone each coordinate is at most \(t\). Since \(B\ge4\) and \(t\ge2\), \(1+2t/B\le t\), giving a bound stronger than the stated \((6t)^q\). Mixed derivatives of total order two cost at most \((q+1)^4\).

## 2. Exact admissible Poisson shell weights

Put

\[
E_p(z)=e^{-z}\sum_{l=0}^p\frac{z^l}{l!},\qquad
a_j=Z2^j,\qquad \tau_j=p/a_j,
\]

and

\[
W_{j,p}(S)=E_p(a_jS)-E_p(a_{j+1}S).
\tag{D6}
\]

These are exact functions, not probabilistic approximations. Their useful positivity and localization follow from

\[
E_p'(z)=-e^{-z}z^p/p!,\qquad
W_{j,p}(S)=\int_{a_jS}^{2a_jS}e^{-z}z^p/p!\,dz.
\tag{D7}
\]

The partition telescopes:

\[
\sum_{j=j_0}^J W_{j,p}(S)
=E_p(a_{j_0}S)-E_p(a_{J+1}S).
\tag{D8}
\]

Let \(I(t)=t-1-\log t\). From \(p!\ge(p/e)^p\), (D7), and its first two derivatives, the following estimates hold, with an absolute constant \(C_0\), for \(i=0,1,2\). Write \(W_p(t)=E_p(pt)-E_p(2pt)\):

\[
\begin{array}{ll}
t^i|W_p^{(i)}(t)|\le C_0(p+1)^3e^{-pI(2t)},&0<t\le1/4,\\
|W_p^{(i)}(t)|\le C_0(p+1)^3,&1/4\le t\le2,\\
t^i|W_p^{(i)}(t)|\le C_0(p+1)^3t^3e^{-pI(t)},&t\ge2.
\end{array}
\tag{D9}
\]

For the first line, the density is increasing on the integration interval, so its upper endpoint bounds the integral. For the last line it is decreasing, so the lower endpoint does. Differentiating the density gives \((p/z-1)e^{-z}z^p/p!\), which proves the derivative cases with the displayed polynomial factors. The middle line follows from the same formulas and \(I\ge0\). All constants here are independent of scale, degree, and shell number.

The elementary estimates

\[
I(2t)\ge1/8+\tfrac12\log(1/(4t))\quad(t\le1/4),
\]

\[
I(t)\ge1/4+\log(t/2)\quad(t\ge2)
\tag{D10}
\]

follow by differentiating with respect to \(\log t\), using \(I(1/2)=\log2-1/2>1/8\) and \(I(2)=1-\log2>1/4\).

## 3. Physical H² conversion and error bound

There is an absolute constant, for example \(1000\), with this property. If \(g\) is a reduced distance function and

\[
|\partial^\nu g|\le F_i(S)\quad(|\nu|=i,\ i=0,1,2)
\]

in half-perimetric coordinates, then its physical lift satisfies

\[
\|g\|_{H^2_*}^2\le10^6\int_0^\infty
\{S^5(F_0^2+F_1^2+F_2^2)+S^3F_1^2\}\,dS.
\tag{D11}
\]

The analogous local bound integrates only over the corresponding \(S\)-range. This follows by the chain rule for \(r,s,u\); their gradients are bounded, and their Hessians have norms \(\sqrt2/r,\sqrt2/s,2\sqrt2/u\). The exact angular integrations are

\[
\int G(S)dx=\frac{8\pi^2}{15}\int G(S)S^5dS,
\]

\[
\int\frac{G(S)}{r^2}dx=\int\frac{G(S)}{s^2}dx
=\frac{16\pi^2}{3}\int G(S)S^3dS,
\qquad
\int\frac{G(S)}{u^2}dx=\frac{16\pi^2}{9}\int G(S)S^3dS.
\tag{D12}
\]

For the last identity integrate first over the angle between electrons, obtaining \((8\pi^2/rs)\log(S/|r-s|)\), then put \(r=vS\) and use \(\int_0^1v(1-v)\log(1/|2v-1|)dv=2/9\). The linear coordinate change to \(a,b,c\) has bounded fixed coefficients. These calculations also prove integrability across all pair sets; no pair cutoff is introduced.

There are no hidden weak-derivative defects in (D11). On a small pair cylinder away from the triple vertex the reduced first derivatives are bounded; the surface flux is \(O(\epsilon^2)\). At the triple sphere, the first derivative of a function satisfying (D1) is \(O(\rho^{\sigma-1})\), so the flux is \(O(\epsilon^{\sigma+4})\). Both vanish. Integrating by parts on domains with these neighborhoods removed and passing to the limit identifies the square-integrable classical derivatives with weak derivatives. The same argument applies to the distance-polynomial witnesses and products in this proof.

Choose

\[
p=256(q+1),\qquad J=p,
\tag{D13}
\]

and define \(P_j(x)=\tau_j^\sigma Q_{\tau_j,q}(x/\tau_j)\). Take
\(0<\delta\le\min(\delta_*,1,1/Z)\). For all sufficiently large \(q\), choose the smallest \(j_0\ge0\) with

\[
a_{j_0}\ge4p/\delta.
\]

The explicit conditions \(4p/\delta>Z\) and \(2^p\ge8p/(Z\delta)\) suffice to ensure

\[
j_0\le J,\qquad \delta/8<\tau_{j_0}\le\delta/4.
\tag{D14}
\]

Let \(D_S=\delta/64\) and consider the region \(S<D_S\). Define

\[
v_q=f_0E_p(ZS)+\sum_{j=j_0}^J W_{j,p}(S)P_j.
\tag{D15}
\]

For the target \(f+f_0\), subtract (D15) using the telescoping identity. The four errors are the constant error, outer omission, inner omission, and the sum of shell approximation errors.

On the fitted shell \(1/4\le S/\tau_j\le2\), (D3), (D9), the product rule, and (D11) give

\[
\|W_{j,p}(f-P_j)\|_{H^2_*,\mathrm{fitted}}
\le C(p+1)^3\tau_j^{\sigma+1}e^{-b\sqrt q}.
\tag{D16}
\]

The power \(\tau_j^{\sigma+1}\) is the physical six-dimensional second-derivative scaling: volume contributes \(\tau_j^3\) to a norm, and two derivatives cost \(\tau_j^{-2}\).

For \(t=S/\tau_j\le1/4\), the first inequality of (D10) bounds the weight by \(e^{-p/8}(4t)^{p/2}\). Multiplying the possible factors \(t^{\sigma-i}\), \(i\le2\), from (D1) or the bounded polynomial derivatives from (D4), all integrals in (D11) are elementary powers with exponent greater than minus one. This gives at most \(C(p+1)^3(q+1)^4\tau_j^{\sigma+1}e^{-p/16}\).

For \(t\ge2\), (D4) and (D10) give

\[
(6t)^qe^{-pI(t)}
\le12^qe^{-p/4}(t/2)^{q-p}.
\tag{D17}
\]

The square of this expression, with the worst remaining volume and derivative powers, is bounded by a constant times

\[
12^{2q}e^{-p/2}\int_2^\infty t^{13}(t/2)^{2q-2p}dt.
\]

The integral is explicit and finite for \(p>q+7\); \(\log12<3\) and (D13) absorb its prefactor into \(Ce^{-p/8}\). The contribution of \(f\) itself is smaller, because \(\sigma<1\). Thus, after harmless enlargement of constants,

\[
\|W_{j,p}(f-P_j)\|_{H^2_*(S<D_S)}
\le C(p+1)^3(q+1)^4\tau_j^{\sigma+1}
[e^{-b\sqrt q}+e^{-p/16}].
\tag{D18}
\]

Only values of \(f\) in \(S<D_S<\delta_*\) were used. Integrating upper estimates to infinity in (D17) is an upper bound, not an assertion of exterior regularity of \(f\).

Since \(\tau_{j+1}=\tau_j/2\), summing the shell estimates costs at most

\[
\sum_{j=j_0}^J\tau_j^{\sigma+1}
\le\frac{(\delta/4)^{\sigma+1}}{1-2^{-(\sigma+1)}}.
\tag{D19}
\]

For the outer omission \(f(1-E_p(a_{j_0}S))\), one has \(S/\tau_{j_0}<1/8\). Integrating the gamma density from zero to its upper limit, and then using its first two derivatives, gives the same exponentially small bound as the lower tail above. The constant error \(f_0(1-E_p(ZS))\) is controlled identically, since \(ZS\le1/64\) and \(p\ge256\).

For the inner omission \(fE_p(a_{J+1}S)\), split at \(S=2\tau_{J+1}\). Below this radius the bounds (D1) and the derivative formulas for \(E_p\) give \(C(p+1)^3\tau_{J+1}^{\sigma+1}\) by (D11). Above it use \(I(t)\) and (D10). Hence the full error obeys

\[
\begin{aligned}
\|f+f_0-v_q\|_{H^2_*(S<D_S)}
\le C(p+1)^3(q+1)^4\big[
e^{-b\sqrt q}+e^{-p/16}
+(p/Z)^{\sigma+1}2^{-(\sigma+1)(J+1)}\big].
\end{aligned}
\tag{D20}
\]

The constants depend only on the original fixed analytic bounds, \(\sigma,\delta,Z,|f_0|\), and the explicit fixed extension cover. No such constant depends on \(j,q,p,J\), or on an untracked shrinking domain. Since \(p=J=256(q+1)\), polynomial prefactors are absorbed by reducing the positive constant multiplying \(\sqrt q\).

## 4. Exact dictionary index

Each term in \(E_p(a_jS)P_j\) has node \(Z2^j\) and polynomial degree at most \(p+q\). The adjacent term in (D6) has node \(Z2^{j+1}\) and the same degree. Therefore

\[
v_q\in V_{N(q)}^{(Z)},\qquad
N(q)=p+q+2(J+1)=769q+770.
\tag{D21}
\]

The constant approximant in (D15) has index \(p\), which is smaller. Ordinary polynomials in \(a,b,c\) become ordinary distance polynomials under the linear inverse coordinate transformation; symmetry under \(a\leftrightarrow b\) is precisely electron exchange symmetry.

For general sufficiently large \(n\), take \(q=\lfloor(n-770)/769\rfloor\), provided it satisfies the two explicit conditions preceding (D14). Monotonicity of the original dictionary and (D20) prove (D2) on \(B_D\) with \(D=D_S/\sqrt2\), since \(S\le\sqrt2\rho\). Use the zero approximant and enlarge \(C\) for the finitely many smaller indices. Every witness has the original deterministic node set; no arbitrary exponential locations, logarithmic basis terms, negative powers, or external cutoff occur in it.

## 5. What remains after this local implication

Each witness is globally in physical \(H^2\), being a finite polynomial in distances times decaying exponentials. The same tail estimates also bound the global norm of every shell term by a polynomial in \(p,q\); the constant term \(E_p(ZS)\) has a polynomial global norm because its principal region has radius proportional to \(p/Z\). Thus the proof does not hide an infinite-norm or nonadmissible local witness.

It does **not** prove that the witness matches the physical wavefunction outside the local region. In particular, the constant approximant stays appreciable up to radii comparable to \(p/Z\). Polynomial boundedness of this exterior mass is insufficient for a small global graph residual. Closing the global theorem still requires a single dictionary witness approximating the physical target on the exterior region while controlling that same witness's tail. RWA alone is not a substitute for this final physical/exterior approximation premise.
