> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Constructive coefficient descent for an analytic KS lift

Evidence category: **paper proof**, with an exact finite polynomial procedure.
No Lean verification, physical eigenfunction construction or executable
energy solver is claimed.

This proof replaces the quantitative source step implicated by
ISSUE_KS_SOURCE_DEGREE_v1.md. It proves descent directly by elementary
polynomial algebra, including the correct degree of the second coefficient,
explicit complex radii, C2 and all-order derivative bounds. It needs no
harmonic-polynomial decomposition or sphere-spectrum result.

## 1. Precise theorem

Let \(d\ge0\) be an integer, \(s\in\mathbb C^d\), and \(y\in\mathbb C^4\).
Fix \(M_y,M_s\ge1\), \(M\ge0\). Suppose \(u(y,s)\) is holomorphic on
\[
 |y|_\infty<M_y^{-1},\qquad |s|_\infty<M_s^{-1},
\]
is bounded there by \(M\), and its restriction to real arguments is invariant
under the simultaneous rotation
\[
 z_1\mapsto e^{i\theta}z_1,\qquad z_2\mapsto e^{i\theta}z_2,
 \quad z_1=y_1+iy_2,\quad z_2=y_3+iy_4,                           \tag{D1}
\]
whenever both real arguments lie in the domain. This invariance holds in
particular when \(u\) is the actual pullback of a function by the KS map
\[
 K(y)=\bigl(2(y_1y_3+y_2y_4),\
           2(y_2y_3-y_1y_4),\
           y_1^2+y_2^2-y_3^2-y_4^2\bigr).
\]
Set
\[
 D=32M_y^2.
\]
There exist uniquely determined holomorphic functions \(A(X,s),B(X,s)\) on
\[
 |X|_\infty<D^{-1},\qquad |s|_\infty<M_s^{-1}                     \tag{D2}
\]
such that on real arguments with \(X=K(y)\) in this neighborhood,
\[
 u(y,s)=A(K(y),s)+|y|^2 B(K(y),s).                               \tag{D3}
\]
Consequently an actual pullback \(u(y,s)=\Psi(K(y),s)\) satisfies
\[
 \Psi(X,s)=A(X,s)+|X|B(X,s)                                     \tag{D4}
\]
for all real \(X,s\) in (D2).

For \(r=|X|_\infty<D^{-1}\), \(h=|s|_\infty<M_s^{-1}\), the bounds are
\[
 |A(X,s)|\le {M\over(1-Dr)(1-M_sh)^d},\qquad
 |B(X,s)|\le {MD\over(1-Dr)(1-M_sh)^d}.                           \tag{D5}
\]
Here a spectator product with \(d=0\) is interpreted as one. On the half
polydisc the bounds are \(2^{d+1}M\) and \(2^{d+1}MD\).

On the quarter polydisc, Cauchy's formula gives, for all multi-indices,
\[
\begin{split}
 |\partial_X^\alpha\partial_s^\gamma A|
 &\le2^{d+1}M\,\alpha!\gamma!(4D)^{|\alpha|}(4M_s)^{|\gamma|},\\
 |\partial_X^\alpha\partial_s^\gamma B|
 &\le2^{d+1}MD\,\alpha!\gamma!(4D)^{|\alpha|}(4M_s)^{|\gamma|}.
\end{split}                                                       \tag{D6}
\]
Thus in particular every C2 bound and every mixed derivative has explicit
constants. For a family with the same radii and a common amplitude \(M\),
the same constants work for every member. If \(u\) is real on the real
domain, \(A,B\) are also real there.

The theorem asserts local analytic-plus-distance structure, not that \(B\)
vanishes at the collision. Its constant term can be nonzero.

## 2. Taylor coefficients and the circle-invariant polynomial pieces

Cauchy's estimate gives the absolutely convergent expansion
\[
 u(y,s)=\sum_{\beta\in\mathbb N_0^4,\ \gamma\in\mathbb N_0^d}
             c_{\beta\gamma}y^\beta s^\gamma,\qquad
 |c_{\beta\gamma}|\le M M_y^{|\beta|}M_s^{|\gamma|}.                \tag{D7}
\]
Let \(P_{j,\gamma}\) be the homogeneous degree-\(j\) polynomial in \(y\)
at spectator multi-index \(\gamma\). The invariance (D1), on a real ball
contained in the polydisc, implies invariance of each \(P_{j,\gamma}\).
Indeed compare coefficients of real radial scaling and of \(s\) in the
identity for \(u\). Each resulting polynomial identity on a real open set
holds identically. In particular all odd \(j\) vanish.

For clarity, use independent complex polynomial variables
\[
 z_1,z_2,w_1,w_2.
\]
On the real slice \(w_i=\overline z_i\), and the inverse linear substitution is
\[
 y_1=(z_1+w_1)/2,\quad y_2=(z_1-w_1)/(2i),\quad
 y_3=(z_2+w_2)/2,\quad y_4=(z_2-w_2)/(2i).                        \tag{D8}
\]
The coefficient L1 norm of a polynomial is the sum of the absolute values
of its coefficients. Every linear form in (D8) has coefficient L1 norm one;
substitution therefore cannot increase this norm.

Under (D1), a monomial \(z^\mu w^\nu\) acquires the factor
\(e^{i(|\mu|-|\nu|)\theta}\). Integrating this finite identity over the
circle shows that an invariant polynomial consists solely of balanced
monomials, with \(|\mu|=|\nu|\). This is a polynomial identity in independent
\(z,w\): the inverse change (D8) is invertible and an identity for all real
\(y\) extends to the complex polynomial ring. Equivalently, one can discard
all unbalanced coefficients. No bound is lost by doing so.

Thus at each lifted degree \(2m\) there are \(m\) factors of \(z\) and \(m\)
of \(w\). The initial coefficient norm has the bound
\[
 \|P_{2m,\gamma}\|_{\rm coef,1}
 \le M M_s^{|\gamma|} M_y^{2m}\binom{2m+3}{3}.                    \tag{D9}
\]

## 3. Pairing monomials and reducing the radial variable

For a balanced monomial
\[
 z_1^{a_1}z_2^{a_2}w_1^{b_1}w_2^{b_2},
 \qquad a_1+a_2=b_1+b_2=m,
\]
choose nonnegative integers \(n_{ij}\) whose row sums are \(a_i\) and
column sums are \(b_j\). This is an explicit procedure: set
\[
 n_{11}=\min(a_1,b_1),\quad n_{12}=a_1-n_{11},\quad
 n_{21}=b_1-n_{11},\quad n_{22}=m-n_{11}-n_{12}-n_{21}.
\]
The last number is nonnegative, since it equals \(\min(a_2,b_2)\).
Then the monomial is \(\prod_{i,j}(z_iw_j)^{n_{ij}}\).

Introduce four polynomial variables \(X_1,X_2,X_3,r\), and replace
\[
 z_1w_1=(r+X_3)/2,\quad z_2w_2=(r-X_3)/2,\quad
 z_1w_2=(X_1+iX_2)/2,\quad z_2w_1=(X_1-iX_2)/2.                 \tag{D10}
\]
Each replacement again has coefficient L1 norm one. The result is a
homogeneous polynomial of degree \(m\) in \((X,r)\), of coefficient norm
no greater than (D9).

On the actual real KS image, \(r=|y|^2=|X|\), and
\[
 r^2=X_1^2+X_2^2+X_3^2.
\]
For every monomial, replace \(r^{2\ell}\) by
\((X_1^2+X_2^2+X_3^2)^\ell\), and replace \(r^{2\ell+1}\) by \(r\)
times that polynomial. This gives exactly
\[
 P_{2m,\gamma}(y)
     =A_{m,\gamma}(K(y))+|y|^2B_{m-1,\gamma}(K(y)),               \tag{D11}
\]
where \(A_{m,\gamma}\) is homogeneous of degree \(m\), and
\(B_{m-1,\gamma}\) is homogeneous of degree \(m-1\).
At \(m=0\), set \(B_{-1,\gamma}=0\). Its degree is never treated as zero
or as degree \(m\).

The coefficient norm of the replacement for \(r^{2\ell}\) is \(3^\ell\).
Therefore the sum of the two output coefficient norms satisfies
\[
\begin{split}
 \|A_{m,\gamma}\|_{\rm coef,1}+\|B_{m-1,\gamma}\|_{\rm coef,1}
 &\le M M_s^{|\gamma|}M_y^{2m}
          \binom{2m+3}{3}3^{\lfloor m/2\rfloor}\\
 &\le M M_s^{|\gamma|}D^m.                                    \tag{D12}
\end{split}
\]
The coarse last inequality holds for all \(m\ge0\): the count
\(\binom{2m+3}{3}\) is at most \(4^{2m}=16^m\), because each multi-index
contributes at least one to the multinomial sum \(4^{2m}\), and
\(3^{\lfloor m/2\rfloor}\le2^m\). At \(m=0\), both factors equal one.

This elementary coefficient argument tracks possible cancellations safely
by the triangle inequality; it never bounds a degree-\(m-1\) polynomial
by \(|X|^m\). The parameter \(\gamma\) is unchanged at every step.

## 4. Normal convergence on an explicit complex domain

Define
\[
 A(X,s)=\sum_{\gamma}\sum_{m\ge0}A_{m,\gamma}(X)s^\gamma,\qquad
 B(X,s)=\sum_{\gamma}\sum_{m\ge1}B_{m-1,\gamma}(X)s^\gamma.
                                                                  \tag{D13}
\]
For \(|X|_\infty=r<D^{-1}\), (D12) gives respectively the bounds
\[
 M M_s^{|\gamma|}(Dr)^m,\qquad
 M M_s^{|\gamma|}D^m r^{m-1}.
\]
The sums over \(m\) are \(M/(1-Dr)\) and \(MD/(1-Dr)\).
The spectator sum is bounded by the exact product
\[
 \sum_{\gamma}M_s^{|\gamma|}|s^\gamma|
       =\prod_{j=1}^d(1-M_s|s_j|)^{-1}
       \le(1-M_s|s|_\infty)^{-d}.                               \tag{D14}
\]
Thus both series converge normally on compact subsets of (D2), are
holomorphic there, and satisfy (D5). The zero-degree term of \(A\) is
included explicitly. The \(B\) series starts at \(m=1\), retaining its
possibly nonzero constant term.

To check agreement with the actual lift, let real \(X\) satisfy (D2).
The KS map is onto, with a preimage satisfying \(|y|^2=|X|\). For example,
when \(|X|+X_3>0\), take
\[
 z_1=\sqrt{(|X|+X_3)/2},\qquad
 z_2=(X_1-iX_2)/(2z_1);
\]
on the remaining negative axis take \(z_1=0,z_2=\sqrt{|X|}\).
At \(X=0\), take zero. The resulting real \(y\) satisfies
\[
 |y|_\infty\le|y|
       =\sqrt{|X|}\le3^{1/4}\sqrt{|X|_\infty}
       <{3^{1/4}\over\sqrt{32}M_y}<M_y^{-1}.                     \tag{D15}
\]
Every preimage has the same Euclidean norm, so every such preimage is inside
the original real polydisc. Equation (D11) holds at each finite homogeneous
degree; normal convergence of the new series and absolute convergence of
the original Taylor series allow passage to the limit. This proves (D3)
and, for an actual pullback, (D4).

The half-domain bounds follow from (D5). On the quarter domain a Cauchy
circle of radius \(1/(4D)\) in each \(X\) coordinate and \(1/(4M_s)\) in
each \(s\) coordinate fits in the half domain; taking limiting radii if
necessary gives (D6).

## 5. Uniqueness, real coefficients and finite constructive content

Suppose analytic germs \(A,B\) have \(A(X,s)+|X|B(X,s)=0\) for real
arguments near \((0,0)\). Fix real \(s\) and a real unit vector \(v\).
For positive \(\tau\), the analytic one-variable function
\[
 A(\tau v,s)+\tau B(\tau v,s)
\]
vanishes. Analytic continuation in \(\tau\) gives the same equation at
negative \(\tau\), whereas the original equality gives
\(A(\tau v,s)-\tau B(\tau v,s)=0\). Hence \(B\) and then \(A\) vanish
on every such line, on a real neighborhood, and thus as holomorphic germs.
The identity theorem on the connected polydisc proves uniqueness throughout
(D2). The same argument applied to conjugate coefficients shows that a lift
real on real arguments has real descended coefficients.

At every finite degree the construction is an actual terminating algebraic
procedure:

1. Substitute (D8) into the input polynomial.
2. Discard unbalanced monomials, justified by the invariance hypothesis.
3. Pair exponents by the displayed nonnegative \(n_{ij}\).
4. Substitute (D10) and expand.
5. Reduce even powers of \(r\), and separate the terms independent of \(r\)
   from those linear in \(r\).

For Gaussian-rational input coefficients, every operation is rational
arithmetic on real and imaginary parts. Different valid pairing choices
give the same final \(A,B\), by uniqueness. The coefficient norm estimate
(D12) is uniform in the chosen pairing.

This finite conversion procedure does not supply the physical Taylor
coefficients of an unknown eigenfunction. It is therefore not, by itself,
an executable physical approximation or energy algorithm. No arithmetic
operation count is represented here as a bit-complexity theorem.

## 6. Exact repair of the source estimate

The archived primary text, equation (4.41) on printed p. 20, assigns
\(|X|^m\) on the right to a polynomial homogeneous of degree \(m-1\).
The example \(u(y,s)=|y|^2\), corresponding to \(\Psi(X,s)=|X|\), has
\(A=0,B=1\), and disproves that literal radial factor at \(m=1\).
Our bound for a degree-\(m-1\) component instead has radial power \(m-1\),
as explicitly used before (D14). The degree-zero term of the first
coefficient is also retained. This repairs the local proof dependence;
it does not refute the source's analytic-plus-distance theorem.

The primary reference is Fournais, Hoffmann-Ostenhof, Hoffmann-Ostenhof and
Sørensen, Analytic structure of many-body Coulombic wave functions,
[arXiv:0806.1004](https://arxiv.org/pdf/0806.1004), Proposition 4.4.
Only the identified source step is at issue here. Sections 2–5 independently
prove every algebraic and convergence fact used in this new theorem, so no
uninspected harmonic-analysis reference is a premise.

## 7. Physical use and remaining boundary

The preceding weak removability, H12 and factorial lemmas give a common
holomorphic polydisc and an amplitude bound \(C\) for the normalized actual
difference \(v_\varepsilon=(u_\varepsilon-a_0)/\varepsilon\), conditional on
the physical solution and regularity hypotheses stated there. Multiplying
back by \(\varepsilon\) gives a holomorphic bound \(C\varepsilon\) for the
unscaled lifted difference \(u_\varepsilon-a_0\). Choose a fixed smaller
polydisc centered at \((y,s)=(0,0)\) within its retained real chart margin
and apply this descent theorem to that unscaled difference, with
\(M=C\varepsilon\) and fixed \(M_y,M_s\). For the two-electron case
\(d=3\), (D5)–(D6) then give common Cartesian analytic coefficients in
\[
 U_\varepsilon(X,t)-a_0
       =A_\varepsilon(X,t)+|X|B_\varepsilon^{\rm dec}(X,t),
\]
each bounded by a fixed multiple of \(\varepsilon\) on the chosen smaller
domain. The superscript distinguishes the descended coefficient from the
operator's zeroth-order potential.

This establishes the quantitative coefficient descent after a uniform actual
KS lift, at paper level. It supplies explicit complex bounds, rather than
only real-polynomial convergence. Rotational invariance of the physical
state, descent to the three ordinary distances at collinear points,
compatibility of boundary germs, a finite normalized-shell cover, physical
spectral hypotheses and formal verification remain separate.

The same algebraic theorem is valid for every finite spectator dimension
\(d\), with the displayed \(2^{d+1}\) bound on the half domain. It addresses
an isolated pair chart and does not handle intersections of arbitrary
many-particle collision strata by itself. No novelty claim or general
efficient many-electron algorithm follows.

## 8. Frozen sources and new provenance

Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660.
Annotated tag: theorem-t-proof-freeze-2026-09-09.
Frozen paths are relative to THEOREM_T_FREEZE_2026-09-09_212604/.

| Frozen source | SHA-256 | Use |
|---|---|---|
| helium_research/sources/regularity_fournais2009_0806.1004.pdf | 1d4e7195084f15c6fd59e1fa0df083dc76d85334ad222aadea5e94a38aecd848 | Exact source typo, independently confirmed in the archived PDF, printed p. 20 |
| rwa_proof/KS_SOURCE_AUDIT.md | 0cada7c07aeb7a0680ad4b2e26977beff8c1de3250086c8196eb25d3a94db08f | Identifies the quantitative descent dependency |
| rwa_proof/RWA_THEOREM.md | d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09 | Uniform Cartesian descent target in section 5 |

New local source rendering: KS_DESCENT_SOURCE_p20_v1.png, SHA-256
12e1e0f9769625a22004bc690ad2632c76bb5dc94b8703111af8ab5f66cd51e0.
The web PDF screenshot service failed; rendering the preserved local PDF
resolved the displayed formula.

Immutable initial issue: ISSUE_KS_SOURCE_DEGREE_v1.md, SHA-256
ff68ffd8925a5056c74bdc2df16a788d5a4f9c6ff7e49ba41114016c1cf6786c.
A new issue disposition will bind the completed reviewed correction by hash.
The initial issue and all frozen sources remain unchanged.

The auxiliary ks_descent_checks_v1.py implements the finite polynomial
conversion over exact Gaussian rationals and checks reconstruction on
specified invariant polynomials. It is a finite diagnostic and does not
replace the proof of normal convergence above. Independent review, final
source hashes and precise test results are recorded separately when sealed.
