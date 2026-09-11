> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Continuum moments and the rational H₂ certificate

This file proves the mathematical interpretation of `matrix.py` and
`check_trial.py`. The proofs and Python computations are outside Lean. They
concern the unbounded-space, infinite-nuclear-mass Coulomb operator, with no
potential or spatial cutoff and with nuclear repulsion excluded.

## Operator, symmetry, and trial domain

The nuclei are at \(R_\pm=(0,0,\pm7/10)\), each with charge one. On the scalar
space \(L^2(\mathbb R^6;\mathbb C)\),

\[
H=-\tfrac12(\Delta_1+\Delta_2)
 -\sum_{i=1}^2\sum_{\nu=\pm}|x_i-R_\nu|^{-1}
 +|x_1-x_2|^{-1}.
\]

Coulomb multipliers are infinitesimally Laplacian-bounded by sliced Hardy
bounds. Kato–Rellich gives the self-adjoint operator with domain \(H^2\) and
form domain \(H^1\). The physical space is the simultaneous-exchange
antisymmetric subspace of \(L^2(\mathbb R^6;\mathbb C^4)\), with the same
spatial domain in each spin component.

Let \(G=\{1,S,J,SJ\}\), where \(S\) exchanges the electrons and \(J\) inverts
both electron positions. These are commuting unitary involutions, and each
commutes with \(H\). For a rational symmetric positive-definite \(2\times2\)
matrix \(A\) and rational axial centers \(p=(p_1,p_2)\), define

\[
g_{A,p}(x)=\exp[-\sum_{d=1}^3(x^d-p^d)^TA(x^d-p^d)],
\qquad p^1=p^2=0,\quad p^3=p,
\]

where \(x^d=(x_{1d},x_{2d})\). Each basis function is the **sum**, without
division by four, \(\phi_{A,p}=\sum_{U\in G}Ug_{A,p}\). Repeated images are
retained. The rational trial is \(\Phi=\sum_jc_j\phi_{A_j,p_j}\).

Every primitive is a Schwartz function: positive definiteness bounds its
exponent below by a positive multiple of the squared distance from its
center, and every derivative is a polynomial times that Gaussian. A finite
linear combination therefore belongs to \(H^2(\mathbb R^6)\). Its product with
the normalized spin singlet \((\uparrow\downarrow-\downarrow\uparrow)/\sqrt2\)
is antisymmetric and lies in the physical operator domain. Thus

\[
S=\|\Phi\|^2,\quad H_1=\langle\Phi,H\Phi\rangle,\quad
H_2=\|H\Phi\|^2
\]

all exist. No membership in \(D(H\circ H)\) is needed for this spectral second
moment. The trial coefficients and all matrix and center parameters are
rational strings in the supplied JSON; positive definiteness is checked by
the exact two-dimensional determinant test.

## Product Gaussian and first kinetic moment

For primitives \(g_i=g_{A,p}\) and \(g_j=g_{B,q}\), put

\[
W=A+B,\quad V=W^{-1},\quad \mu=V(Ap+Bq),\quad
\xi=p^TAp+q^TBq-\mu^TW\mu\ge0.
\]

Completing squares gives

\[
g_i g_j=e^{-\xi}\exp[-(x-\mu)^T(W\otimes I_3)(x-\mu)],\qquad
\int g_i g_j=\pi^3 s_{ij},\quad
s_{ij}=e^{-\xi}(\det W)^{-3/2}. \tag{1}
\]

Here and below only the axial component of the mean is nonzero. Expectations
denoted \(\mathbb E\) use the normalized product Gaussian. Its covariance in
each physical coordinate is \(V/2\).

Set \(B_i=A^2\), \(B_j=B^2\), \(d_i=\mu-p\), and \(d_j=\mu-q\). Applying the
kinetic operator to a primitive gives the actual polynomial

\[
K_i(x):=\frac{-\Delta g_i/2}{g_i}
=3\operatorname{tr}A-2\sum_{d=1}^3(x^d-p^d)^TB_i(x^d-p^d).
\]

Its expectation is

\[
k_i=3\operatorname{tr}A-3\operatorname{tr}(B_iV)-2d_i^TB_id_i. \tag{2}
\]

The exchanged expression gives \(k_j=k_i\). This also follows by integration
by parts: Gaussian decay removes the boundary term and
\(\langle g_i,-\Delta g_j/2\rangle=\langle-\Delta g_i/2,g_j\rangle\).
The code checks this equality with exact rational arithmetic.

## Full squared-action moment

There are five inverse-distance terms. Index them by \(\alpha\), using

\[
(v_\alpha,z_\alpha,q_\alpha)=
(e_1,\pm7/10,-1),\ (e_2,\pm7/10,-1),\ ((1,-1),0,+1),
\]

and write \(C_\alpha(x)=|v_\alpha^Tx-z_\alpha e_3|^{-1}\). Then

\[
Hg_i=(K_i+\sum_\alpha q_\alpha C_\alpha)g_i.
\]

The Gaussian fourth-moment identity gives

\[
\mathbb E(K_iK_j)=k_i k_j
 +6\operatorname{tr}(B_iVB_jV)+8d_i^TB_iVB_jd_j. \tag{3}
\]

To verify (3), the covariance of two quadratic forms in a Gaussian with
covariance \(\Sigma=V/2\) is

\[
2\operatorname{tr}(B_i\Sigma B_j\Sigma)
 +4d_i^TB_i\Sigma B_jd_j.
\]

There are three independent physical-coordinate copies of the trace term,
only one nonzero mean copy, and the factors \(-2\) in \(K_i,K_j\) multiply
this covariance by four. This produces exactly the coefficients 6 and 8.

For a single potential put

\[
a=v^TVv>0,\quad m=v^T\mu-z,\quad d=Vv,\quad T=m^2/a.
\]

The Gaussian integral representation of \(1/r\) changes the mean and
covariance to

\[
\mu(t)=\mu-t^2dm/a,\quad
\Sigma(t)=\tfrac12(V-t^2dd^T/a),\quad 0\le t\le1.
\]

Consequently

\[
\mathbb E(K_iC)=\frac2{\sqrt{\pi a}}
 \left[k_iF_0(T)+b_{i,2}F_1(T)+b_{i,4}F_2(T)\right], \tag{4}
\]

where \(F_n(T)=\int_0^1t^{2n}e^{-Tt^2}\,dt\),

\[
b_{i,2}=\frac3a d^TB_id+\frac{4m}a d_i^TB_id,\qquad
b_{i,4}=-\frac{2m^2}{a^2}d^TB_id.
\]

The same tilted covariance with the constant polynomial gives
\(\mathbb E C=2F_0(T)/\sqrt{\pi a}\).

Finally the exact primitive moments divided by \(\pi^3\) are

\[
\begin{aligned}
S_{ij}&=s_{ij},\\
(H_1)_{ij}&=s_{ij}\left[k_j+\sum_\alpha q_\alpha\mathbb E C_\alpha\right],\\
(H_2)_{ij}&=s_{ij}\left[
\mathbb E K_iK_j+
\sum_\alpha q_\alpha\mathbb E((K_i+K_j)C_\alpha)
 +\sum_{\alpha,\beta}q_\alpha q_\beta\mathbb E(C_\alpha C_\beta)
\right]. \tag{5}
\end{aligned}
\]

The final sum has five diagonal terms and twice each of the ten unordered
off-diagonal terms. Its signs are kept. Formula (5) differentiates and
integrates in the continuum; it is unrelated to squaring the projected
finite Hamiltonian matrix.

Every double-Coulomb expectation in (5) has a smooth one-dimensional integral
or a closed special-function expression. The complete independent derivation
is in [moment_audit.md](moment_audit.md); the implemented quadrature and its
explicit remainder proof are in [quadrature.md](quadrature.md). These files
treat independent linear forms, identical centers, and distinct axial
centers separately. No Coulomb singularity is ignored by a quadrature grid.

## Symmetry factors and contraction

For each of the three operators/inner products in (5), unitarity and
commutation with \(G\) imply

\[
\langle\phi_i,O\phi_j\rangle
=4\sum_{U\in G}\langle g_i,OUg_j\rangle.
\]

For the squared-action moment interpret the left side as
\(\langle H\phi_i,H\phi_j\rangle\); the same identity holds without applying
the operator square. Thus all matrices omit the **same \(4\pi^3\)**. Summing

\[
\sum_i c_i^2M_{ii}+2\sum_{i<j}c_ic_jM_{ij}
\]

then gives the trial moment with that factor removed. Joint symmetry and
interchange of the primitive pair may be used to merge identical integrals.
The code's canonical-pair cache uses exactly these operations, and sums
the signed rational contraction weights before evaluation. Cancellation is
performed with exact integers/Fractions or directed intervals, never with
floating-point signs.

## Enclosure algebra and error allocation

The arithmetic library stores dyadic rational endpoints. Addition,
multiplication, division, integer square roots, and every other operation
round outward. The exponential, Boys, arctangent, erfc, and quadrature
remainders are explicit in `quadrature.md` and the interval source. Finite
quadrature resource limits can return a wider interval; the actual width,
not a requested tolerance, enters the certificate.

Let the computed intervals be \(S\in[S_-,S_+]\),
\(H_1\in[A_-,A_+]\), and \(H_2\in[Q_-,Q_+]\), with \(S_->0\). Interval
division encloses \(m=H_1/S\). Computing \(H_2/S-m^2\) with outward square
arithmetic encloses \(v\). Intersect only its lower endpoint with zero,
using the exact identity \(v=\|(H-m)\Phi\|^2/\|\Phi\|^2\ge0\).

The separate [separator proof](separator.md) and rational one-electron
certificate establish \(\beta=-91/50\) in the invariant sector containing
the physical ground. If \(m\in[m_-,m_+]\), \(m_+<\beta\), and \(v\le v_+\),
Temple gives

\[
m_- -\frac{v_+}{\beta-m_+}\le E_0\le m_+. \tag{6}
\]

The independently proved bound \(H\ge h_1+h_2\ge-66/25\) can improve a very
loose lower endpoint by taking its maximum with \(-66/25\). The certificate
retains the raw Temple value so this improvement cannot be mistaken for a
small residual. Final decimal endpoints are outward rounded by exact integer
floor/ceiling and are themselves rational numbers.

An optional weighted error budget accelerates very small contracted terms.
For each nonzero primitive-pair contribution with signed rational weight
\(w_j\) and normalized overlap upper bound \(s_{j,+}>0\), choose any positive
rational \(q_j\) satisfying
\[
q_j\ge\sqrt{|w_j|s_{j,+}},\qquad Q=\sum_jq_j.
\]
Thus \(q_j\) may be an outward rational upper bound on that square root.
For a positive rational total budget \(\eta\), allocate
\[
\varepsilon_j=
\frac{\eta S_-q_j}{25Q|w_j|s_{j,+}}.
\]
Zero contraction weights are removed exactly before allocation, so every
denominator here is positive.

If each double-Coulomb interval meets width \(\varepsilon_j\), its
contribution to the width of \(H_2/S\), before other interval and rounding
errors, is at most \(\eta q_j/Q\). Indeed the sum of absolute products of
the five potential charges is \(25\), and
\[
\frac{25|w_j|s_{j,+}\varepsilon_j}{S_-}
=\frac{\eta q_j}{Q}.
\]
Summing over contributions proves the total budget \(\eta\). The final
interval always uses actual computed bounds, even when a requested width
was not reached.

For negligible terms the universally valid Cauchy–Schwarz bound

\[
0\le\mathbb E(C_\alpha C_\beta)
\le2/\sqrt{a_\alpha a_\beta}
\]

may already fit the allocated width. It follows from
\(\mathbb E C_\alpha^2\le2/a_\alpha\), itself immediate from the exact
inverse-square integral. This is a proved coarse enclosure, not a dropped
matrix element.

## Verification and trust boundary

`independent_audit.py` derives the kinetic polynomials by direct Cartesian
differentiation and evaluates Gaussian moments by an independent
integration-by-parts recurrence. It also checks the Coulomb formulas against
independent series, exact limits, and the uneliminated two-dimensional
integral. These are exact arithmetic checks supplementing the paper proofs.

Trial optimization and floating quadrature are explicitly untrusted
candidate-selection tools. The checker reads rational coefficients and
parameters, verifies the domain-relevant SPD conditions, and recomputes the
moments. It does not trust an optimizer eigenvalue, floating variance, or
published reference. Use a fresh final run to recreate all pair-cache
entries. The source and trial hashes identify the computation.

The scalar/finite-dimensional Lean theorems prove their displayed arithmetic
implications. The continuum realization, positivity/HVZ argument, Gaussian
integral identities, and Python arithmetic execution remain outside Lean.
