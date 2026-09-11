> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Exact dyadic approximation of the physical angular logarithm

Status: **PROVEN** (elementary paper proof in this session; not a Lean theorem).
This is a component of the necessary leading-singularity gate. It makes no
claim about the complete physical eigenfunction or global RATE.

## Statement and conventions

Write $x,y\in\mathbb R^3$, $r=|x|,s=|y|,u=|x-y|$,

\[
 S=r+s,\quad \rho=(r^2+s^2)^{1/2},\quad q=x\cdot y=(r^2+s^2-u^2)/2.
\]

Fix an integer $Z\ge2$, and retain precisely the user's dictionary

\[
 V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
 e^{-Z2^jS}\mathcal P_{n-2j}^{\rm sym}(r,s,u).
\]

Here the polynomials have nonnegative integer powers of $r,s,u$, are invariant
under exchanging $r,s$, and have total degree at most the displayed degree.
The norm used below is the physical Cartesian Sobolev norm

\[
 \|f\|_{H^2_*}^2=\int_{\mathbb R^6}
 (|f|^2+|\nabla f|^2+\|D^2f\|_F^2)\,dx\,dy.
\]

This counts the mixed second derivatives twice. It dominates the ordinary
multi-index $H^2$ norm, and is equivalent to it with a universal constant.

Define, for $d=0,1,2$,

\[
 M_d(Z)=\left[\frac{8\pi^2}{15}
 \frac{(2d+5)!}{(2Z)^{2d+6}}\right]^{1/2},
\]

\[
 C_Z=64M_0(Z)+(2+8Z)M_1(Z)+(1+Z+Z^2)M_2(Z),
\]

\[
 D_Z=63\cdot10^6\cdot17^8\cdot11^{11} Z^{-3}.
\]

**Angular component theorem.** There are explicitly constructed $g_n\in
V_n^{(Z)}$, all with rational polynomial coefficients, such that

\[
 f_{\rm ang}=e^{-ZS}q\log(\rho/S),\qquad
 \|f_{\rm ang}-g_n\|_{H^2_*}
 \le (9C_Z+2D_Z)\exp\left(-\frac{\log2}{52}n\right)
 \quad(n\ge0).
\]

The value at $x=y=0$ is its continuous extension. In particular the same bound
holds on every physical ball $B_\delta\subset\mathbb R^6$. The constants are
deliberately loose. A scalar coefficient multiplying this component multiplies
the norm bound by its absolute value.

## 1. Angular expansion, including all pair edges

Set $a=2rs/S^2$. Then $0\le a\le1/2$, and

\[
 \log(\rho/S)=\tfrac12\log(1-a)
 =-\tfrac12\sum_{k=1}^{\infty}\frac{a^k}{k}.
\]

This is an identity for the actual angular factor, not a replacement by a
radial model. All terms are symmetric in $r,s$. The representation contains
negative powers of $S$ only at this intermediate analytic stage.

Put $F_k=q a^k$. Away from $r s=0$, elementary Cartesian differentiation
gives the safe estimates

\[
 |F_k|\le\tfrac14 S^2 2^{-k},\qquad
 |\nabla F_k|\le2(k+1)S2^{-k},\qquad
 \|D^2F_k\|_F\le64k^2 2^{-k}.                 \tag{A1}
\]

Here are details for the possible singular terms. One has

\[
 |a_r|\le 2s/S^2,\quad |a_s|\le2r/S^2,\quad
 |a_{rr}|,|a_{ss}|\le8/S^2,\quad |a_{rs}|\le12/S^2,
\]

and $q\le rs$ in absolute value, $\|D^2q\|_F=\sqrt6$,

\[
 |q|\,\|D^2a\|_F\le13,\qquad |\nabla a|\le2/S.
\]

The $a_r/r,a_s/s$ terms in the physical radial Hessian are included in the
bound 13: their contribution is at most

\[
 \sqrt2 rs\left(\frac{2s}{rS^2}+\frac{2r}{sS^2}\right)
 \le2\sqrt2.
\]

The remaining block contributions are at most (2+2+6). Applying the product
and chain rules to $q a^k$ now gives

\[
 \|D^2(q a^k)\|_F
 \le [3+8k+4k(k-1)+26k]2^{-k}\le64k^2 2^{-k}.
\]

The estimate of the term with two derivatives of $a$ uses

\[
 |q|a^{k-2}|\nabla a|^2\le2a^{k-1}\le4\,2^{-k}.
\]

For $k=1$ that term has coefficient $k(k-1)=0$, so no division by zero
at $a=0$ is performed. All estimates extend weakly across the axes: near
$r=0,s>0$, $q a^k$ has the factor $x\cdot y\,r^k$, times a smooth
function of the positive variable $s$ and the Lipschitz variable $r$.
It is $C^1$, its second derivatives are locally bounded, and no surface
distribution occurs. The same holds at $s=0$. At the triple origin,
(A1) gives function $O(S^2)$, gradient $O(S)$, and bounded weak Hessian.

There is no independent singular derivative at $u=0$: $q=x\cdot y$ is a
Cartesian polynomial. In the final distance-polynomial expression its
$u^2$ occurrence is exactly the same polynomial, not an uncancelled cusp.
Collinear configurations are ordinary Cartesian points and introduce no
extra coordinate singularity into these estimates.

Using $\|\nabla S\|=\sqrt2$,

\[
 |F_k|\|D^2S\|_F\le2S2^{-k},
\]

the product rule for $e^{-ZS}F_k$, and the exact radial identity

\[
 \int_{\mathbb R^6}h(S)\,dx\,dy
 =\frac{8\pi^2}{15}\int_0^\infty h(S)S^5\,dS,
\]

give

\[
 \|e^{-ZS}F_k\|_{H^2_*}\le C_Z(k+1)^2 2^{-k}.       \tag{A2}
\]

For example the Hessian is bounded pointwise by $e^{-ZS}2^{-k}$ times

\[
 64k^2+[2Z+6Z(k+1)]S+\tfrac12 Z^2 S^2,
\]

and the lower derivatives are bounded by $S^2/4$ and
$2(k+1)S+ZS^2/2$. The displayed $C_Z$ bounds their $L^2$ norms by the
triangle inequality. Consequently the angular series converges in physical
$H^2_*$, and its tail satisfies

\[
 \left\| f_{\rm ang}
 +\frac12e^{-ZS}q\sum_{k=1}^{K}\frac{a^k}{k}\right\|_{H^2_*}
 \le\frac{C_Z}{2}(K+5)2^{-K}.                    \tag{A3}
\]

Indeed $(k+1)^2/k\le k+3$ and
$\sum_{k>K}(k+3)2^{-k}=(K+5)2^{-K}$.

## 2. Eliminate the forbidden inverse powers by allowed exponentials

For $S>0$,

\[
 e^{-ZS}S^{-2k}
 =\frac1{(2k-1)!}\int_Z^\infty
 (\lambda-Z)^{2k-1}e^{-\lambda S}\,d\lambda.       \tag{A4}
\]

Thus the $k$-th summand of $f_{\rm ang}$ equals

\[
 -\frac{2^{k-1}}{k(2k-1)!}
 \int_Z^\infty(\lambda-Z)^{2k-1}
 q(rs)^k e^{-\lambda S}\,d\lambda.               \tag{A5}
\]

For $\operatorname{Re}\lambda>0$, write
$U_k(\lambda)=q(rs)^k e^{-\lambda S}$, as an element of the complexification
of $H^2_*$. It is holomorphic there: differentiation in $\lambda$ multiplies
the function by $-S$, and all such difference quotients and their first two
Cartesian weak derivatives are dominated on compact subsets of that half
plane by a polynomial times a strictly decaying exponential.

For $\ell\ge Z\ge2$ and $ |\lambda-\ell|\le3\ell/4$, the following
uniform norm estimate will be used:

\[
 \|U_k(\lambda)\|_{H^2_*}
 \le {\cal M}_k\ell^{-2k-3},\qquad
 {\cal M}_k=10^6(k+2)^2 2^{2k}\sqrt{(4k+13)!}.     \tag{A6}
\]

To verify it directly, each Cartesian derivative of order $d\le2$ is
bounded in absolute value by

\[
 12(k+2)^2 S^{2k+2-d}(1+|\lambda|S)^2
 e^{-(\operatorname{Re}\lambda)S}.
\]

One can check this by writing
$q(rs)^k=\sum_{i=1}^3(x_i r^k)(y_i s^k)$. The second derivatives of
$x_i r^k$ are bounded by $(k+2)^2r^{k-1}$ for $k\ge1$, with the
obvious analogous zeroth- and first-order estimates. These factors also show
directly that the asserted derivatives are weak derivatives at the axes.
On the circle, $|\lambda|\le7\ell/4<2\ell$ and
$\operatorname{Re}\lambda\ge\ell/4$. Substitute $v=\ell S$ in the
radial integral. For $b\le4k+9$,

\[
 \int_0^\infty v^b(1+2v)^4e^{-v/2}\,dv
 \le625\,2^{4k+10}(4k+13)!.
\]

There are 43 ordered derivatives counted in the norm; using
$\sqrt{43}<7$, $\sqrt{8\pi^2/15}<3$, and $\ell\ge1$ gives (A6)
with ample room in $10^6$.

Estimate (A6), at real $\lambda$, makes (A5) absolutely Bochner integrable
in $H^2_*$ at infinity: after multiplication by its weight the norm is
$O_k(\lambda^{-4})$. Hence (A4)--(A5), initially pointwise off the origin,
are also identities in the physical Sobolev space.

## 3. Dyadic bands and the exact polynomial witness

Let $\lambda_j=Z2^j$. Use contiguous bands

\[
 I_0=[Z,3Z/2],\qquad
 I_j=[3\lambda_j/4,3\lambda_j/2]\quad(j\ge1).
\]

Every $\lambda\in I_j$ satisfies $|\lambda-\lambda_j|\le\lambda_j/2$.
Taylor expansion in the Banach space about the permitted exponent
$\lambda_j$, to degree $P$, gives

\[
 U_k(\lambda)\approx q(rs)^k e^{-\lambda_jS}
 \sum_{b=0}^{P}\frac{[-(\lambda-\lambda_j)S]^b}{b!}.
\]

Cauchy's estimate on the circle of radius $3\lambda_j/4$ gives the
uniform remainder bound

\[
 3{\cal M}_k\lambda_j^{-2k-3}(2/3)^{P+1}.         \tag{A7}
\]

For $K,P,J\ge1$, define the completely explicit finite witness

\[
 G_{K,P,J}=-\sum_{k=1}^{K}\frac{2^{k-1}}{k(2k-1)!}
 q(rs)^k\sum_{j=0}^{J}e^{-\lambda_jS}
 \sum_{b=0}^{P}\frac{(-S)^b}{b!}
 \int_{I_j}(\lambda-Z)^{2k-1}(\lambda-\lambda_j)^b\,d\lambda.
                                                        \tag{A8}
\]

Every integral in (A8) is of an ordinary polynomial over rational endpoints.
For complete explicitness, if $I_j=[A_j,B_j]$, it equals

\[
 \sum_{a=0}^{2k-1}\sum_{c=0}^{b}
 {2k-1\choose a}{b\choose c}
 (-Z)^{2k-1-a}(-\lambda_j)^{b-c}
 \frac{B_j^{a+c+1}-A_j^{a+c+1}}{a+c+1}.
\]

Thus all coefficients are rational. The only functions in the final witness
are $e^{-Z2^jS}q(rs)^kS^b$; expanding $q$ and $S^b$ gives ordinary
symmetric distance polynomials of degree $2+2k+b$. In particular

\[
 G_{K,P,J}\in V_{P+2K+2J+2}^{(Z)}.              \tag{A9}
\]

There are no logarithms, inverse powers, cutoffs, or additional exponents in
the witness. Values $n<28$ below will use the zero witness, which is an
element of every $V_n^{(Z)}$.

## 4. Remainder estimates with explicit constants

The elementary factorial inequality

\[
 \frac{\sqrt{(4k+13)!}}{(2k-1)!}
 \le(4k+13)^8 2^{2k-1}                           \tag{A10}
\]

follows by separating the last 15 factorial factors and then using
${4k-2\choose2k-1}\le2^{4k-2}$.

For the finite-band Taylor error, multiply (A7) by the weight in (A5), use
$\int_{I_j}(\lambda-Z)^{2k-1}d\lambda\le(3\lambda_j/2)^{2k}$, apply
(A10), and sum $\sum_{j\ge0}\lambda_j^{-3}=(8/7)Z^{-3}$. The result is

\[
 E_{\rm Taylor}\le6\cdot10^6 Z^{-3}
 K(K+2)^2(4K+13)^8 72^K(2/3)^{P+1}.             \tag{A11}
\]

For the omitted Laplace tail, the last retained endpoint is
$L_J=3Z2^J/2$. Bound the weight by $\lambda^{2k-1}$, use (A6) at real
$\lambda$, and integrate $\int_{L_J}^{\infty}\lambda^{-4}d\lambda
=1/(3L_J^3)$. Again (A10) gives the safe bound

\[
 E_{\rm Laplace\ tail}\le10^6 Z^{-3}
 K(K+2)^2(4K+13)^8 32^K2^{-3J}.                 \tag{A12}
\]

These are estimates in the physical global $H^2_*$ norm, not merely in
pointwise or energy norm.

Take $K=m,P=16m,J=4m$, $m\ge1$. The dictionary index is $26m+2$.
Since $72(2/3)^{16}<1/8$, and $32\cdot2^{-12}=2^{-7}$, (A11)--(A12)
sum to at most

\[
 7\cdot10^6 Z^{-3}m(m+2)^2(4m+13)^8 2^{-3m}
 \le D_Z2^{-m}.                                 \tag{A13}
\]

For the last inequality use $m(m+2)^2(4m+13)^8\le9\cdot17^8m^{11}$ and
$m^{11}2^{-2m}\le11^{11}$, a consequence of $\log2\ge1/2$.
Combining (A3) and (A13) proves

\[
 \|f_{\rm ang}-G_{m,16m,4m}\|_{H^2_*}
 \le [\tfrac12 C_Z(m+5)+D_Z]2^{-m}.              \tag{A14}
\]

For $n\ge28$ take $m=\lfloor(n-2)/26\rfloor$. Then (A9) places the
witness inside the exact $V_n^{(Z)}$. Since
$(m+5)2^{-m/2}\le9$, $m\ge(n-28)/26$, and $2^{28/52}<2$, (A14)
implies the theorem's displayed rate. For $0\le n<28$, use $g_n=0$
and (A2), which give $\|f_{\rm ang}\|_{H^2_*}\le5C_Z/2$. The same
constant $9C_Z+2D_Z$ covers these finitely many indices.

## 5. Coefficient heights and what has not been claimed

For fixed $Z$, the endpoints and exponents in (A8) have bit length $O(m)$.
The polynomial integrals have degree at most $2k-1+b=O(m)$; their binomial
coefficients and factorial divisors have bit length $O(m\log m)$. Expanding
and summing their rational expressions gives polynomial bit length, for
example a deliberately coarse $O_Z((m+1)^8\log(m+2))$ bound per collected
coefficient suffices even when denominators are combined without exploiting
common factors. There are only polynomially many summands. The numerator and
denominator sizes may be $2^{\operatorname{poly}(m)}$; their bit lengths
remain polynomial. This claim concerns this explicit component witness,
not an assumed coefficient bound for the full ground state.

The theorem does not require an unproved all-order Fock expansion. It handles
exactly the angular part of the verified physical leading logarithm through
$\log\rho=\log S+\log(\rho/S)$. The radial part $q e^{-ZS}\log S$ is
a separate scalar component. The physical cusp multiplier $e^{u/2}$, an
actual localizing factor, and the nonconstant physical remainder are not
silently included in this theorem. Their multiplication/approximation must
be accounted for separately; multiplying by an arbitrary $C^\infty$
factor does not automatically preserve an exponential approximation rate.

In particular this closes an angular representation issue. It neither proves
the full physical graph RATE nor gives a counterexample to it.
