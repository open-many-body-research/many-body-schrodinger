> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Constructive dyadic approximation of the radial logarithmic component

Status: **PROVEN** (paper proof in this session; not a Lean theorem).

This lemma concerns only `q exp(-Z S) log S`. The physical factor
`q log(r²+s²)` also has an angular component. This file does not claim that
the radial component alone closes the physical singularity gate.

## Statement and exact dictionary accounting

Let `x,y ∈ R³`, `r=|x|`, `s=|y|`, `u=|x-y|`, `S=r+s`, and

\[
q=x\cdot y=(r^2+s^2-u^2)/2.
\]

Fix an integer `Z≥2`. Use the physical Cartesian Sobolev norm

\[
\|v\|_{H^2}^2=\|v\|_2^2+\|\nabla v\|_2^2
                  +\|D^2v\|_{L^2(\mathrm{Frob})}^2.
\]

For every integer `n≥4`, put

\[
J=\lfloor n/4\rfloor,\qquad p=n-2J-2,\qquad d=p+1.
\]

There is an explicitly specified `g_n∈V_n^(Z)` such that, globally on
`R⁶`,

\[
\boxed{\|q e^{-ZS}\log S-g_n\|_{H^2}
\le Z^{-3}\left[3200(n+4)^5 2^{-n/2}
                  +12000\,2^{-3n/4}\right].}
\tag{R1}
\]

Consequently the same estimate holds on every ball `B_δ`. It gives an
exponential rate after absorbing the displayed polynomial into a constant.
There is no negative distance power in the approximants.

The spin-singlet factor, normalized to have spin norm one, leaves all the
spatial estimates unchanged and makes these exchange-symmetric functions
fermionically antisymmetric.

## 1. Exact Laplace representation

For `S>0`, Frullani's identity (or differentiation in `S` followed by
evaluation at `S=1`) gives

\[
\log S=\int_0^\infty\frac{e^{-t}-e^{-St}}t\,dt.
\]

Define the finite real constant

\[
c_Z=\int_0^{Z/2}\frac{e^{-t}-1}{t}\,dt
       +\int_{Z/2}^{\infty}\frac{e^{-t}}t\,dt.
\]

Thus `|c_Z|≤2+log Z`. Splitting the integral and putting `λ=Z+t` gives

\[
e^{-ZS}\log S=c_Ze^{-ZS}
 +e^{-ZS}\int_0^{Z/2}\frac{1-e^{-tS}}t\,dt
 -\int_{3Z/2}^{\infty}\frac{e^{-\lambda S}}{\lambda-Z}\,d\lambda.
\tag{R2}
\]

All subsequent integrals converge in the `H²` norm after multiplication by
`q`; the bounds below prove this, including convergence at both endpoints.

For `a_j=Z2^j`, the panels

\[
I_j=[3a_j/4,3a_j/2],\qquad j=1,2,\ldots
\]

partition `[3Z/2,∞)` up to endpoints. The expansion node on each panel is
exactly the prescribed dictionary exponent `a_j`, not a shifted or optimized
node.

Set

\[
P_p(S)=\sum_{k=1}^{p}\frac{(-1)^{k+1}(Z/2)^k}{k\,k!}S^k,
\qquad
w_{jk}=\frac{(-1)^k}{k!}\int_{I_j}
              \frac{(\lambda-a_j)^k}{\lambda-Z}\,d\lambda.
\]

Empty sums are zero. The promised approximant is

\[
g_n=q\left[e^{-ZS}(c_Z+P_p(S))
       -\sum_{j=1}^J e^{-a_jS}\sum_{k=0}^p w_{jk}S^k\right].
\tag{R3}
\]

Every polynomial `q S^k` is exchange symmetric in `(r,s)` and has ordinary
distance degree `k+2≤p+2=n−2J≤n−2j` at node `j≤J`. The base-node head also
has degree at most `n`. Hence (R3) belongs to the exact dictionary in the
request. This argument uses no cutoffs, reciprocal powers, new exponents,
or shell-dependent basis functions.

## 2. Physical Cartesian derivative estimate

Away from the measure-zero pair-collision sets,

\[
|q|\le S^2/4,\quad |\nabla q|\le S,\quad
\|D^2q\|_F=\sqrt6,\quad |\nabla S|=\sqrt2,
\quad |q|\|D^2S\|_F\le\sqrt2 S.
\]

The last inequality follows from
`||D²S||_F²=2/r²+2/s²` and `|q|≤rs`.
Thus, for a scalar function `F(S)`,

\[
\begin{aligned}
|qF|&\le S^2|F|/4,\\
|\nabla(qF)|&\le S|F|+(\sqrt2/4)S^2|F'|,\\
\|D^2(qF)\|_F&\le \sqrt6|F|+3\sqrt2 S|F'|
                                      +(S^2/2)|F''|.
\end{aligned}\tag{R4}
\]

Radial integration in the two physical three-dimensional electron variables
gives exactly

\[
\int_{\mathbb R^6} G(S)\,dx\,dy
 =\frac{8\pi^2}{15}\int_0^\infty G(S)S^5\,dS.
\tag{R5}
\]

Indeed `16π²∫₀ˢ r²(S−r)² dr=(8π²/15)S⁵`.
The square root of this geometric factor is less than `3`.

These are weak-derivative statements as well. On `r=0` or `s=0`, the
distance Hessian has its ordinary locally integrable `1/r` or `1/s`
singularity, without a surface delta; this follows by integrating twice
on the complement of radius-ε tubes, whose boundary terms vanish. At the
six-dimensional origin the logarithmic terms satisfy (R4) with square
integrable right-hand sides. The same tube/ball argument therefore proves
`H²` membership of the target and every finite approximant.

## 3. Uniform Taylor remainder in H²

Let `a≥1`, `−a/4≤h≤a/2`, `d≥1`, and

\[
E_{a,h,d}(S)=e^{-(a+h)S}
    -e^{-aS}\sum_{k=0}^{d-1}\frac{(-hS)^k}{k!},\qquad
b=a+\min(h,0).
\]

Integral Taylor remainder and its first two `S` derivatives imply

\[
|E_{a,h,d}^{(\ell)}(S)|
\le |h|^d e^{-bS}
 \sum_{i=0}^{\min(\ell,d)}{\ell\choose i}
       (a+|h|)^{\ell-i}\frac{S^{d-i}}{(d-i)!},
\quad \ell=0,1,2.
\tag{R6}
\]

For clarity, (R6) follows by differentiating

\[
\frac{(-h)^d S^d}{(d-1)!}
  \int_0^1(1-t)^{d-1}e^{-(a+th)S}\,dt.
\]

For every integer `m≥0`, the elementary central-binomial estimate gives

\[
\left(\int_0^\infty
       \left|\frac{S^m}{m!}e^{-bS}\right|^2S^5\,dS\right)^{1/2}
 =\frac{\sqrt{(2m+5)!}}{2^{m+3}m!b^{m+3}}
 \le (m+3)^3 b^{-m-3}.
\tag{R7}
\]

Use `(2m)!≤4^m(m!)²` and bound the five remaining factors by
`(2m+6)^5`; their square root is at most `(2m+6)^3`.

Write `||·||₅` for the norm in `L²((0,∞),S⁵dS)`.
Since `3a/4≤b≤a` and `a+|h|≤3a/2`, (R6)–(R7) yield, for
`0≤v≤2`, `0≤ℓ≤2`,

\[
\|S^v E_{a,h,d}^{(\ell)}\|_5
 \le 3^\ell(4/3)^{v+3}(d+v+3)^{v+3}
       a^{\ell-v-3}(|h|/b)^d.
\tag{R8}
\]

To check the factorial bookkeeping, put `m=d−i+v` in (R7), use
`m!/(d−i)!≤(d+v)^v`, and sum the binomial factors bounded by
`(b+a+|h|)^ℓ≤(3a)^ℓ`.

For precisely the six `(ℓ,v)` pairs used in (R4), `ℓ≤v`. Their scalar
coefficients sum to less than `9`, and
`3^ℓ(4/3)^(v+3)<40`. Combining with the factor less than `3` in (R5)
therefore proves the convenient uniform bound

\[
\boxed{\|qE_{a,h,d}\|_{H^2}
 \le1200(d+5)^5 a^{-3}(|h|/b)^d.}
\tag{R9}
\]

On every chosen panel, `|h|/b≤1/2` (and on its negative side it is at
most `1/3`). This is why these panels work; expanding indiscriminately
over `[a,2a]` would not give this geometric factor by the same estimate.

The analogous direct estimate, from (R4) and (R7) with `v=0,1,2`, is

\[
\|q e^{-\lambda S}\|_{H^2}\le3000\lambda^{-3}
\quad(\lambda\ge1).
\tag{R10}
\]

For example the six terms are bounded by `3` times
`250/4 + 64 + 3·250/8 + 5·27/2 + 9·64/2 + 250/2`, which is below `3000`.

## 4. Summing head, panels, and omitted scales

For the head in (R2), keep the factor `(t/Z)^d` in (R9); integrating
`dt/t` gives

\[
\text{head error}\le
1200(d+5)^5 Z^{-3}\frac{2^{-d}}d.
\]

Each panel has positive weight

\[
\int_{I_j}\frac{d\lambda}{\lambda-Z}
=\log\frac{3a_j/2-Z}{3a_j/4-Z}\le\log4<2.
\]

Consequently the total retained-panel error is at most

\[
2400(d+5)^5 2^{-d}\sum_{j=1}^J a_j^{-3}
\le\frac{2400}{7}(d+5)^5 Z^{-3}2^{-d}.
\]

The discarded integral begins at `L=3a_J/2≥3Z`. There
`λ−Z≥2λ/3`. Minkowski's inequality and (R10) give

\[
\text{tail error}\le4500\int_L^\infty\lambda^{-4}d\lambda
 =1500L^{-3}\le1500Z^{-3}2^{-3J}.
\]

Their sum is bounded by

\[
1600Z^{-3}(d+5)^5 2^{-d}+1500Z^{-3}2^{-3J}.
\]

Finally `d≥n/2−1`, `d+5≤n+4`, and `J≥n/4−1` prove (R1).
For example `2^42 Z^{-3}2^{-n/4}` is a conservative bound for (R1)
when `n≥4`: `(n+4)^5 2^{-n/4}<2^28`, using `log2≥1/2` and maximizing
`(n+4)^5e^{-n/8}`. The finitely many smaller indices can use `g_n=0`
and an enlarged fixed constant, so the existence assertion holds for all
`n≥0` as well.

## 5. Coefficients and limits of this lemma

The head polynomial has rational coefficients. Each `w_jk` is a rational
linear combination of `1` and the logarithm of a positive rational:
substitute `y=λ−Z`, expand `(y+Z−a_j)^k/y`, and integrate each monomial.
Moreover

\[
|w_{jk}|\le2\frac{(a_j/2)^k}{k!},\qquad |c_Z|\le2+\log Z.
\]

For `j,k≤n` and fixed `Z`, these magnitudes have `O(n²)` bit length.
The rational factors produced by the displayed finite formula also have
polynomial bit height. Expanding `qS^k` into ordinary monomials adds at
most exponential-in-`k` integer factors and therefore only polynomial
bit length. The constant `c_Z` is one fixed real coefficient, equivalently
`−γ−log(Z/2)`; membership in the real/complex dictionary does not require
this coefficient itself to be rational. This is a RATE witness, not an
interval-arithmetic certificate. Rational rounding can use the existing
finite-dictionary precision machinery; no new moment field is needed to
evaluate rationally rounded trials.

This proves no approximation statement for `q log(ρ/S)`, no all-order
Fock expansion, and no global ground-state RATE. Its global `H²` norm is
strong enough to imply the same local norm or, through the established
Coulomb graph-norm bound, a graph error for this single radial model.
