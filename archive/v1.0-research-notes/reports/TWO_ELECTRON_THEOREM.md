> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

## 1. Statement of Theorem T and which of A/B/C was reached

For each fixed integer \(Z\in\{2,\ldots,Z_{\max}\}\), let \(E_Z\) be the bottom of the spectrum of
\[
H_Z=-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u,
\qquad r=|x_1|,\ s=|x_2|,\ u=|x_1-x_2|.
\]
**Theorem T, still CONJECTURED:** a deterministic algorithm, given the requested precision \(p\ge1\), returns rational endpoints enclosing \(E_Z\), of width at most \(2^{-p}\), in at most \(C_Zp^d\) bit operations. Precision is measured by \(p\), equivalently a unary precision request; it is not measured by the binary input length \(\log p\). The finite charge class needs no separate uniformity argument.

**Outcome: none of stopping conditions A, B, C was reached.** This is the requested fallback B write-up, with the local sublemma in §4 and the other breaks identified. It is **not** a claim that only that sublemma remains. There is an additional, prior failure: the prescribed factor-two *global Rayleigh-variance* minimization loop need not select the ground state. A nested-space counterexample satisfying even exponentially small ground residuals proves that the proposed abstract correctness implication is false (§2). Also, “computable moments” alone does not imply polynomial bit cost (§3). These issues cannot be discharged by proving a local regularity lemma.

The mandatory **Theorem C is PROVEN (paper)** below: for every fixed finite positive exponent set, the normalized ground residual in its nonnegative-power Hylleraas spaces is bounded below by \(c(\Omega+1)^{-72}\). The exponent is a bound from the proof, not an estimate of the observed convergence exponent. This excludes that dictionary's degree-by-degree Temple loop from polynomial precision cost. It does not exclude Fock-augmented, geometrically refined, or expanding-exponent dictionaries.

**PROVEN (paper):** the charge-\(Z\) separator, the continuum Temple certificate, and a modified fixed-shift algorithm's correctness and rate-free termination on an explicit operator core. **PROVEN (Lean):** the scalar consequences described in §6. Neither the continuum analysis nor Theorem C has been formalized here.

\(Z=1\) is excluded as requested: the supplied \(H^-\) ground-energy value lies above \(-5/8\), so this rank-one separator does not support this Temple construction.

## 2. Correctness proof (unconditional)

**The physical operator — PROVEN (paper).** Define
\[
\mathcal H_-=\{\Psi\in L^2(\mathbb R^6;\mathbb C^2\otimes\mathbb C^2):
 \Psi(x_2,\sigma_2;x_1,\sigma_1)=-\Psi(x_1,\sigma_1;x_2,\sigma_2)\}.
\]
Lebesgue measure is used in space and counting measure in spin. The operator acts identically on spin components, with
\[
D(H_Z)=H^2(\mathbb R^6;\mathbb C^4)\cap\mathcal H_-,
\qquad D(q_Z)=H^1(\mathbb R^6;\mathbb C^4)\cap\mathcal H_-.
\]
There is no finite-basis compression or Coulomb cutoff in these definitions.

Sliced three-dimensional Hardy inequalities give, for example,
\[
\|r^{-1}f\|_2\le2\|\nabla_1f\|_2,\qquad
\|u^{-1}f\|_2\le2\|\nabla_1f\|_2.
\]
Together with the analogous \(s\) bound and Fourier interpolation
\(\|\nabla f\|_2\le\epsilon\|\Delta f\|_2+C_\epsilon\|f\|_2\),
these make the Coulomb multiplication operator infinitesimally bounded relative to the Laplacian. Kato–Rellich therefore gives self-adjointness on the displayed domain and equivalence of
\[
\|f\|_{H^2}\quad\text{and}\quad\|f\|_2+\|H_Zf\|_2.
\tag{2.1}
\]
The exchange projection commutes with the operator, so restriction to \(\mathcal H_-\) preserves self-adjointness. In particular, the operator graph norm is stronger than \(H^1\); no \(H^1\) approximation rate is substituted here.

**Separator and existence — PROVEN (paper); its charge arithmetic is PROVEN (Lean).** Put
\[
L_Z=-Z^2,\quad U_Z=-Z^2+\frac{5Z}{8},\quad
\beta_Z=-\frac{5Z^2}{8},\quad
g_Z=\beta_Z-U_Z=\frac{Z(3Z-5)}8>0.
\tag{2.2}
\]
For helium these constants are \(L_2=-4,\ U_2=-11/4,\ \beta_2=-5/2,\ g_2=1/4\). No new helium energy enclosure is being computed.
The one-electron hydrogenic spectrum has ground energy \(-Z^2/2\), with two spin orbitals, and next energy \(-Z^2/8\). Antisymmetrizing their tensor product leaves one doubly occupied \(1s\) determinant at energy \(-Z^2\). Every vector orthogonal to it has noninteracting energy at least \(-5Z^2/8\). If \(P_0\) is its rank-one projection, positivity of \(1/u\) proves the form inequality
\[
H_Z\ge L_ZP_0+\beta_Z(I-P_0).
\tag{2.3}
\]
For the normalized spatial product
\(\chi_Z=(Z^3/\pi)e^{-Z(r+s)}\), multiplied by the unit singlet spinor, the already established hydrogenic Coulomb expectation scales to \(5Z/8\). Thus its mean is \(U_Z<\beta_Z\). This is an analytic charge scaling of the existing identity, not a new numerical integration.

The spectral projection of \(H_Z\) onto \((-\infty,\beta_Z)\) has dimension at most one: a two-dimensional subspace would contain a nonzero vector orthogonal to \(P_0\), contradicting (2.3). The trial mean proves that this projection is nonzero. It therefore consists of one eigenvector. In fact \(E_Z<U_Z\): equality would make the normalized trial a ground eigenvector by the spectral theorem, whereas \(H_Z\chi_Z=(-Z^2+1/u)\chi_Z\) is not a constant multiple of \(\chi_Z\). Consequently
\[
L_Z\le E_Z\le U_Z<\beta_Z,\qquad
\sigma(H_Z)\setminus\{E_Z\}\subset[\beta_Z,\infty),
\quad \beta_Z-E_Z\ge g_Z.
\tag{2.4}
\]
This argument supplies existence as well as simplicity. It does not need an unproved ionization margin. Consistently, HVZ places the essential threshold at the one-electron energy \(-Z^2/2>\beta_Z\).

The scalar spatial ground state can be chosen continuous and strictly positive. Positivity improvement of the Coulomb heat semigroup gives uniqueness in the scalar space; exchange and rotation invariance then give an exchange-symmetric \(S\) state. Its product with the singlet belongs to \(\mathcal H_-\) and realizes the same lowest energy. These observations justify the three-distance representation used in §4–§5; (2.3) itself already applies to the full fermionic space.

**Temple — PROVEN (paper).** Let \(\phi\in D(H_Z)\) have norm one and set
\[
m=\langle\phi,H_Z\phi\rangle,\qquad
v=\|H_Z\phi\|_2^2-m^2=\|(H_Z-m)\phi\|_2^2.
\]
For its spectral measure \(\mu\), (2.4) implies
\[
0\le\int(\lambda-E_Z)(\lambda-\beta_Z)\,d\mu(\lambda)
 =v-(m-E_Z)(\beta_Z-m).
\]
Thus, when \(m<\beta_Z\),
\[
m-\frac{v}{\beta_Z-m}\le E_Z\le m.
\tag{2.5}
\]
Only \(\phi\in D(H_Z)\) is needed. The notation \(\langle H^2\rangle\) here means the quadratic-form value \(\|H\phi\|^2\); it does not require \(\phi\in D(H_Z^2)\).

If rational arithmetic supplies \(m\in[m_-,m_+]\), \(0\le v\le v_+\), and \(m_+<\beta_Z\), the rational certificate is
\[
\left[m_--\frac{v_+}{\beta_Z-m_+},\ m_+\right].
\tag{2.6}
\]
This follows by making both the numerator and reciprocal denominator unfavorable. Outward rounding can only enlarge this interval.

**Why the requested loop is not proved — PROVEN (paper counterexamples).** For a dictionary synthesis map \(\Phi c=\sum c_i\phi_i\), write
\[
G=\Phi^*\Phi,\quad A=\Phi^*H\Phi,\quad Q=(H\Phi)^*(H\Phi).
\]
The Rayleigh variance is
\[
\frac{c^*Qc}{c^*Gc}-\left(\frac{c^*Ac}{c^*Gc}\right)^2.
\tag{2.7}
\]
It is not one generalized Rayleigh quotient. The pencil \(Q-2tA+t^2G\) minimizes a residual at fixed \(t\), not at the coefficient-dependent mean.

The selection failure persists even if (2.7) can be minimized exactly. On \(\ell^2(\mathbb N_0)\), let
\[
He_0=-2e_0,\quad He_1=0,\quad
He_{j+1}=\left(1+\frac1{j+1}\right)e_{j+1}\quad(j\ge1)
\]
and
\[
V_n=\operatorname{span}\{e_1,\ v_1,\ldots,v_n\},
\qquad v_j=e_0+2^{-j}e_{j+1}.
\tag{2.8}
\]
This bounded self-adjoint operator has simple ground \(E=-2\), separator \(\beta=-1\), and
\(H\ge-2P_{e_0}-1(I-P_{e_0})\). The normalized \(v_1\) has mean \(-13/10<\beta\). The spaces are nested, their dimension is \(n+1\), and their Gram, Hamiltonian and squared-action entries are rational of polynomial bit length. Explicitly,
\[
G_{ij}=1+\delta_{ij}4^{-i},\quad
A_{ij}=-2+\delta_{ij}\left(1+\frac1{i+1}\right)4^{-i},
\]
\[
Q_{ij}=4+\delta_{ij}\left(1+\frac1{i+1}\right)^2 4^{-i}
\]
on the \(v_i\) block; \(e_1\) is orthogonal to that block, with entries \(1,0,0\).
Moreover,
\[
\frac{\|(H+2)v_n\|}{\|v_n\|}
=\frac{(3+1/(n+1))\,2^{-n}}{\sqrt{1+4^{-n}}}\le4\,2^{-n}.
\]
Hence even an exponential RATE property holds.

Nevertheless, the only eigenvectors in any finite \(V_n\) are multiples of \(e_1\). Indeed, a ground eigenvector would require all independent tail coordinates to vanish. A higher eigenvector would require all but one tail coefficient to vanish, leaving a nonzero \(e_0\) coefficient. Neither is possible. Variance zero is equivalent to being an eigenvector. The global minimum variance is therefore zero and every factor-two minimizer is \(e_1\), with mean \(0>\beta\). The prescribed loop never obtains a Temple certificate. This is a counterexample to the proposed general bridge, not a counterexample to the atomic Theorem T.

Even rational output has a separate zero-minimum issue: the rational symmetric matrix
\(\left(\begin{smallmatrix}0&1\\1&1\end{smallmatrix}\right)\) has zero minimum variance but no rational eigenvector direction. A multiplicative factor-two guarantee would require exact zero. An additive tolerance avoids this issue.

**A modification that does select the ground branch — PROVEN (paper).** This changes the requested optimization; it is not presented as its implementation. Fix
\[
\sigma=L_Z-1,\qquad d_Z=E_Z-\sigma\in[1,1+5Z/8],
\]
and minimize, with additive tolerance tending to zero,
\[
J_\tau(c)=
\frac{c^*(Q-2\sigma A+\sigma^2G)c+\tau\|c\|^2}{c^*Gc}.
\tag{2.9}
\]
Here \(\tau>0\). Let \(D=Q-2\sigma A+\sigma^2G\) and \(T=D+\tau I\).
Since \(H_Z-\sigma\ge I\), \(D\ge G\) and \(T\ge G+\tau I\). Thus maximizing \(c^*Gc/(c^*Tc)\) is a regularized positive-definite generalized eigenproblem, even for a redundant dictionary.

For any normalized trial let \(\eta=\|(H_Z-E_Z)\phi\|\). The spectral gap implies
\[
m-E_Z\le\frac{\eta^2}{g_Z}.
\]
Therefore
\[
\|(H_Z-\sigma)\phi\|^2-d_Z^2
=\eta^2+2d_Z(m-E_Z)
\le K_Z\eta^2,\qquad
K_Z=1+\frac{2(1+5Z/8)}{g_Z}.
\tag{2.10}
\]
Conversely, a shifted-quotient excess at most \(\varepsilon\) implies
\[
\eta^2\le\varepsilon,\quad m-E_Z\le\varepsilon/2,\quad v\le\varepsilon.
\]
If \(\varepsilon\le g_Z\), then
\[
\beta_Z-m\ge g_Z/2,\qquad
\frac{v}{\beta_Z-m}\le\frac{2\varepsilon}{g_Z}.
\tag{2.11}
\]
These statements do not use a rate.

**Rate-free termination for the modification — PROVEN (paper).** One explicit fallback core is the antisymmetrized span of Cartesian monomials of total degree at most \(n\), times \(e^{-(|x_1|^2+|x_2|^2)}\), with the four spin basis vectors; append \(\chi_Z\). It is nested, has dimension \(O(n^6)\), and lies in \(D(H_Z)\). Rational coefficients suffice. Finite Hermite expansions approximate Schwartz functions in their Schwartz seminorms, and Schwartz functions are dense in \(H^2\). Antisymmetrization is bounded on \(H^2\). Equation (2.1) therefore proves graph density in \(\mathcal H_-\).

All moments of each fixed core are computable by rational interval arithmetic: derivatives are polynomials times Gaussians; singular factors have order at most two or products of two inverse distances. Use Gaussian integral representations of inverse distances, or excise rational collision tubes and a large outer box. The omitted integrals have effective bounds from the explicit polynomial-Gaussian envelope and three-dimensional integrability of \(r^{-2}\); Gaussian tails have factorial-series bounds. On the remaining compact set, ordinary rational quadrature with derivative bounds converges effectively. This establishes computability, without asserting a precision-cost bound for this fallback procedure.

Take persistent basis lists, \(\tau_n=2^{-n}\), and additive solve error \(2^{-n}\). For any fixed graph-close core vector, its coefficient penalty tends to zero as \(n\) increases. The infimum of the unregularized shifted quotient is \(d_Z^2\), so the returned physical shifted quotients converge to \(d_Z^2\). Equation (2.11) gives eventual positive Temple denominators and widths tending to zero. At stage \(n\), compute moment enclosures to absolute quotient accuracy \(2^{-n}\); use the stricter rational acceptance filter \(m_+\le U_Z\), otherwise skip that stage. Since \(E_Z<U_Z\), this filter eventually succeeds too. Apply (2.6) on accepted stages; their denominators are at least \(g_Z\). All stage decisions are finite rational decisions. Every \(p\) eventually stops, without an assumed approximation rate.

This proves computability of \(E_Z\) by a Temple procedure with a corrected objective. It neither proves a polynomial cost nor rescues the factor-two global-variance loop.

## 3. Cost proof conditional on the Rate Lemma, with the polynomial exponent accounting

**The implication requested from RATE alone is not established.** Its wording requires computable moments, not polynomial-time computable moments, and supplies no bound on representation size or useful coefficient size. Regularization needs such a bound to preserve the approximating witness.

This is a logical distinction, independent of the Coulomb problem. Choose a computable real \(b\in(-2,-1)\) that is not polynomial-time computable, and the matrix \(\operatorname{diag}(b,1)\). Its one-dimensional exact ground-state dictionary has zero residual at every order and computable interval moments. A polynomial energy algorithm for this input would compute \(b\) in polynomial time. Such computable reals exist by time-hierarchy/diagonalization. Thus bare computability and an approximation rate cannot imply the asserted complexity in general. This example does not show that atomic moments are hard; those moments need their own proof.

Ko's dyadic Cauchy representation is the convention used here: a \(2^{-p}\) rational enclosure and a dyadic approximation at error \(2^{-p}\) differ by only a constant shift of precision. The primary chapter preview verifies the representation; the full complexity definitions were behind access control. No complexity theorem is attributed to unread pages. [Ko (1991), chapter DOI 10.1007/978-1-4684-6802-1_3](https://link.springer.com/chapter/10.1007/978-1-4684-6802-1_3).

**A conditional cost theorem for (2.9) — PROVEN (paper).** Suppose a particular explicit dictionary has, in addition to RATE:

1. construction cost \(O(n^a)\), dimension \(m_n=O(n^b)\), and polynomial-bit parameter descriptions;
2. moments, including their integer-part sizes, computable to error \(2^{-s}\) in \(O((n+s)^r)\) bit operations per entry;
3. a normalized RATE witness with coefficient norm squared at most \(2^{h(n)}\), where \(h(n)=O(n^q)\) is a fixed integer-valued polynomial bound, enlarged to dominate parameter bit heights and the logarithmic upper bounds on all matrix norms as well.

These are implementation hypotheses here, not consequences silently added to RATE. A redundant dictionary is allowed. Append the anchor and an operator core for unconditional correctness; require the same computational properties for the resulting dictionary.

We may weaken a RATE exponent larger than one to \(\alpha=1\); hence take \(0<\alpha\le1\). Set
\[
\tau_n=2^{-h(n)-n},\qquad \delta_n=2^{-n}.
\]
For the RATE witness, the regularizer costs at most \(2^{-n}\). An additive-\(\delta_n\) solve of (2.9) returns a normalized trial with
\[
\|(H_Z-\sigma)\phi_n\|^2-d_Z^2
\le K_ZC^2e^{-2cn^\alpha}+2^{1-n}.
\tag{3.1}
\]
This uses (2.10), comparison with the witness, and nonnegativity of the returned vector's penalty. Equations (2.11) and (2.6) then give an order \(n\le C'_Z(p+1)^{1/\alpha}\) where the certified width is at most \(2^{-p}\), after allocating a fixed fraction of the tolerance to outward rounding. The stricter filter \(m_+\le U_Z\) also holds beyond a fixed order because \(U_Z-E_Z>0\); that order is absorbed into \(C'_Z\). The unknown constants in RATE affect \(C'_Z\), not correctness or the loop's code.

**Finite solve and precision.** Include the normalized anchor as a dictionary element. Sliced Hardy gives
\(\|(H_Z-\sigma)\chi_Z\|\le1+2Z\). For \(0<\tau\le1\),
\[
B_0^{-1}\le\lambda_\tau:=\max_{c\ne0}\frac{c^*Gc}{c^*Tc}\le1,
\qquad B_0=(1+2Z)^2+1.
\tag{3.2}
\]
If approximations \(\widetilde G,\widetilde T\) have operator error at most \(e\le\tau/2\), every quotient changes by at most \(4e/\tau\). To see this, normalize \(\|c\|=1\); its exact denominator is at least \(\tau\), its approximate denominator is at least \(\tau/2\), and its exact numerator is between zero and that denominator. Subtracting the two fractions proves the bound.

Choose entry precision so that operator error \(m_ne_{\rm entry}\) is at most a fixed multiple of \(\tau_n\delta_n/B_0^2\). Bisect the largest generalized quotient using exact rational PSD tests of \(t\widetilde T-\widetilde G\), retaining a rational negative witness at a lower threshold. Equation (3.2) keeps its quotient bounded away from zero, so inversion changes an additive \(O(\delta_n/B_0^2)\) error into \(O(\delta_n)\). Exact symmetric elimination also handles a zero diagonal: a nonzero entry in its row provides a negative two-coordinate direction; otherwise remove that row. Positive pivots lead to Schur complements. This gives both a PSD decision and a rational negative witness.

Rescale the retained coefficient vector so \(\|c\|_\infty=1\). Its quotient is at least \(1/(2B_0)\), hence
\[
c^*Gc\ge \frac{\tau_n}{2B_0}.
\]
Thus certifying its actual physical moments requires only a polynomial number of guard bits. It does not require an unproved lower Gram eigenvalue. A sufficient entry precision is
\[
s_n=O(h(n)+n+\log m_n),
\tag{3.3}
\]
in addition to the polynomial integer-part bounds already included in the hypotheses. If a stage is evaluating a requested output precision directly, adding \(p\) to this expression remains polynomial.

For rational matrix entries of \(B\) bits, fraction-free elimination represents intermediates by minors, with bit length \(O(m_n(B+\log m_n))\). Schoolbook integer arithmetic gives a conservative PSD-test cost \(O(m_n^5(B+\log m_n)^2)\). The number of bisections is \(O(s_n+\log B_0)\). Witness recovery and rational moment evaluation have the same polynomial character. Singular exact comparisons do not cause an indefinite precision loop: the PSD test is applied to the already fixed rational approximating matrix, and the perturbation allowance accounts for the difference from the true matrix.

Writing \(q'=\max(1,q)\), a per-stage polynomial exponent can therefore be taken as
\[
B_*=\max\{a,\ 2b+rq',\ 5b+3q'\}.
\tag{3.4}
\]
The terms count dictionary construction, \(O(m_n^2)\) moments, and elimination plus bisection, respectively. Summing all stages through \(n=O(p^{1/\alpha})\) gives
\[
O\!\left(p^{(B_*+1)/\alpha}\right).
\tag{3.5}
\]
Round this exponent upward if an integer exponent is desired. This accounting is conditional on the displayed effective dictionary properties. There are no established \(a,b,q,r\) for a dictionary satisfying the atomic graph RATE in this report.

**Normalization/regularization scalar proof — PROVEN (paper and Lean).** If \(N\ge1/4\), \(A\ge0\),
\(q-\lambda N\le A\epsilon^2\), and \(\tau b\le\epsilon^2\), then
\[
\frac{q+\tau b}{N}-\lambda\le4(A+1)\epsilon^2.
\tag{3.6}
\]
Add the two numerator inequalities, divide by \(N>0\), and use \(1/N\le4\). This is the required residual-form analogue of Rayleigh-quotient regularization. It propagates a supplied witness estimate; it does not establish that the witness has polynomial coefficient height.

## 4. Rate Lemma: proof, or the named sub-lemma and where the argument breaks

**Choice for further work: a conforming hp dictionary in perimetric coordinates. CONJECTURED graph RATE.** The reason for choosing it over a Fock-augmented dictionary is that the verified Morgan source does not establish representation of the physical ground eigenfunction by its constructed convergent series. An hp proof could instead use derivative bounds. The following calculations also show why the existing polyhedral theorems cannot simply be quoted.

Use half-perimetric coordinates
\[
a=(s+u-r)/2,\quad b=(r+u-s)/2,\quad c=(r+s-u)/2,
\quad r=b+c,\ s=a+c,\ u=a+b.
\]
For an invariant function \(F(a,b,c)\), the exact spatial measure is
\(16\pi^2w\,da\,db\,dc\), with \(w=(a+b)(a+c)(b+c)\).
Writing
\[
A_0=\frac{ac}{(b+c)(a+b)},\qquad B_0'=\frac{bc}{(a+c)(a+b)},
\]
the reduced Laplacian is
\[
\mathcal L F=w^{-1}\operatorname{div}(wG\nabla F),\qquad
G=\begin{pmatrix}
1+A_0-B_0'&0&-A_0\\
0&1-A_0+B_0'&-B_0'\\
-A_0&-B_0'&A_0+B_0'
\end{pmatrix}.
\tag{4.1}
\]
This follows by applying the chain rule to \(r,s,u\): their principal metric has diagonal \(1,1,2\), zero \(rs\) entry, and cross entries
\((r^2+u^2-s^2)/(2ru)\), \((s^2+u^2-r^2)/(2su)\).
The linear coordinate change yields (4.1). In particular,
\[
\det G=
\frac{abc(a+b+c)((b+c)^2+(a+c)^2)}
{(a+b)^2(a+c)^2(b+c)^2}.
\tag{4.2}
\]
The open octant faces are noncoincident **collinear** configurations; the metric loses rank there. The two-body collisions lie on the axes: \(r=0\) means \(b=c=0\), and analogously for \(s,u\). They are not the open faces. This is a degenerate weighted elliptic problem, not a uniformly elliptic scalar Laplacian on a polyhedron. No artificial Dirichlet condition is justified on these faces.

**Domain and moments for a finite hp space — PROVEN (paper).** A compactly supported, globally \(C^1\), finite piecewise-polynomial \(F\) on the closed octant, with bounded piecewise second derivatives and \(C^1\) matching to zero at its outer boundary, lifts to \(H^2(\mathbb R^6)\). Indeed, the coordinate maps are Lipschitz and, almost everywhere,
\[
|D^2(F\circ(a,b,c))|
\le C\left(|D^2F|+(r^{-1}+s^{-1}+u^{-1})|DF|\right).
\]
Each inverse distance is locally square-integrable because its transverse dimension is three. Matching first derivatives removes interface delta distributions. Exchange symmetrization and multiplication by the singlet give the required fermionic domain membership.

Choose rational mesh vertices and rational polynomial basis coefficients. Omitting the common \(16\pi^2\) factor, the overlap and Hamiltonian moments are rational: \(w\), \(wG\), and \(w(-Z/r-Z/s+1/u)\) are polynomials. Integration by parts is valid for the conforming compactly supported lift. If \(H\phi_i=P_i/w\) on a cell, then
\[
Q_{ij}=\int_{\rm cell}\frac{P_iP_j}{(a+b)(a+c)(b+c)}\,da\,db\,dc.
\tag{4.3}
\]
These are fixed-dimensional rational integrals with integrable boundary singularities, not squared projected Hamiltonian entries. Rational domain subdivision and denominator bounds give certified computability.

There is a concrete route to a polynomial cost for (4.3): on an origin cube, split into its six coordinate orderings and use, in one ordering,
\(a=h\rho,\ b=h\rho t,\ c=h\rho tv\). The Jacobian divided by \(w\) is
\[
[\rho(1+t)(1+v)(1+tv)]^{-1}.
\]
Each \(P_i\) vanishes to total order at least two at the vertex, so the numerator removes the apparent radial singularity. Cells touching one collision axis use the corresponding two-dimensional Duffy substitution. The remaining denominator factors are analytic and bounded away from zero on the reference cube. This identifies a quadrature proof to finish; it is not a completed bit-cost analysis for a global hp generator.

For an independent rational basis with polynomially bounded dimension and entry heights, an exact rational Gram matrix also supplies a bound \(\lambda_{\min}(G)\ge2^{-\operatorname{poly}(n)}\): clear all denominators, use nonzero integer determinant, and bound the other eigenvalues by the trace/operator norm. Thus conditioning can be dealt with constructively if the generator and these entry bounds are supplied.

**Named local sublemma, all quantifiers, CONJECTURED (OPEN).** This is the specific local statement handed to a specialist, not an algorithmic conclusion:
\[
\begin{gathered}
\textbf{Local perimetric weighted analyticity (LPWA).}\\
\text{For every fixed integer }Z\ge2,\text{ let }F_Z\text{ represent its normalized positive }S\text{ ground state}.\\
\exists\,\delta,A,C>0\ \exists\,\sigma_0\in(0,1)\quad
F_Z\text{ extends real-analytically across every face/edge point with }0<\rho<\delta,\\
\forall\nu\in\mathbb N_0^3\ \forall(a,b,c)\in[0,\infty)^3,\quad
0<\rho:=a+b+c<\delta\ \Longrightarrow\\
\left|\partial^\nu(F_Z-F_Z(0))(a,b,c)\right|
\le C A^{|\nu|}|\nu|!\,\rho^{\sigma_0-|\nu|}.
\end{gathered}
\tag{4.4}
\]
The asserted extensions define the derivatives on the boundary strata. The estimate allows the quadratic logarithm and linear distance cusps after reduction.

If (4.4) holds, tensor geometric meshes with innermost scale \(2^{-L}\), degree \(L^2\), and \(C^1\) endpoint-Hermite interpolation are a candidate local construction. There are \(O(L^3)\) tensor cells and \(O(L^6)\) local coefficients, hence \(O(L^9)\) parameters. Cutting off \(F_Z-F_Z(0)\) inside the innermost cube gives a physical graph error bounded by a constant times \(2^{-L(\sigma_0+1)}\): the measure is homogeneous of degree six including volume, and two derivatives contribute the inverse square scale; the angular inverse-distance factors are integrable. On the remaining geometric cells, derivative bounds suggest errors \(e^{-cL^2}\), which can absorb factors \(e^{CL}\).

**Exact break:** a published theorem applying to the degenerate weighted graph operator (4.1), with the boundary meaning in (4.4), has not been verified. Moreover, the entire program still needs written weighted interpolation/gluing estimates, a global tail-and-exterior approximation argument, and polynomial generator/quadrature bounds. Local regularity alone does not prove these. No claim of stopping condition B is made. The prescribed variance optimizer would remain invalid as an abstract selection argument even if all these hp steps were supplied.

**Bounded primary-source audit.** Only the named literature and directly relevant approximation citations were consulted; access failures are part of the record.

| Primary source | Verified content used or checked | What it does not discharge here |
|---|---|---|
| Kato (1957), DOI [10.1002/cpa.3160100201](https://doi.org/10.1002/cpa.3160100201) | Publisher metadata checked; full text unavailable. Its local Lipschitz/cusp result is explicitly discussed in the Fournais primary preprint. | No claim that the inaccessible paper supplies a graph approximation rate. |
| Fournais et al. (2005), [math-ph/0312060](https://arxiv.org/abs/math-ph/0312060), DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6) | Theorem 1.1, equations (1.8)–(1.12), read: explicit exponential factor and \(C^{1,1}\) remainder. Supplies the logarithmic obstruction in §5. | Not all-order weighted analyticity or a graph RATE. |
| Fournais et al. (2009), [0806.1004](https://arxiv.org/abs/0806.1004), DOI [10.1007/s00220-008-0664-5](https://doi.org/10.1007/s00220-008-0664-5) | Theorem 1.4 read: analytic-plus-distance-times-analytic structure at an isolated two-body collision. | Does not include the triple-collision point or supply uniform derivatives approaching it. |
| Fock (1954; 1958 translation) | Original and translation not retrieved; bibliography checked against Morgan's primary reference list. No DOI verified. | No theorem imported from the inaccessible text. |
| Morgan (1986), DOI [10.1007/BF00526420](https://doi.org/10.1007/BF00526420) | Publisher abstract and references read; full paper paywalled. The abstract proves convergence for constructed Fock-type solutions and explicitly discusses physical eigenfunction representability as an open problem. | The supplied premise that this proves the physical ground state's convergent expansion is not verified and cannot be used. |
| Babuška–Guo (1988/1989), DOIs [10.1137/0519014](https://doi.org/10.1137/0519014), [10.1137/0520054](https://doi.org/10.1137/0520054) | Publisher abstracts verified: two-dimensional polygons and the associated trace spaces. Full PDFs redirected to access pages; original theorem numbers and proofs not verified. | No applicable theorem for the three-dimensional degenerate metric (4.1) was verified. |
| Costabel–Dauge–Nicaise (2012), [1002.1772](https://arxiv.org/abs/1002.1772) | Theorem 7.8 checked: analytic weighted regularity under its elliptic-system, coercivity, boundary, and spectral-window hypotheses. | Does not identify (4.1) with that class or prove physical graph interpolation. |
| Maday–Marcati (2019), [1810.09010](https://arxiv.org/abs/1810.09010), DOI [10.1142/S0218202519500295](https://doi.org/10.1142/S0218202519500295) | Corollaries 5 and 11 checked in the accessible preprint: weighted analytic regularity and exponential DG energy-norm approximation with its positive singular-potential hypotheses. Publisher full-text access failed. | Its principal Laplacian and isolated-singularity setting do not establish (4.4) or an \(H^2\) lift rate. |
| Schötzau–Schwab–Wihler (2013), DOI [10.1137/090774276](https://doi.org/10.1137/090774276) | Lemma 5.1 and tensor construction read: derivative-preserving endpoint projectors; equation (5.9) gives mixed-derivative estimates. | Existence of a \(C^1\) projector alone is not the missing weighted physical error estimate. |
| Braess (1995), DOI [10.1006/jath.1995.1110](https://doi.org/10.1006/jath.1995.1110) | Primary abstract checked for hydrogenic exponential-sum approximation; full theorem norms unavailable. | No verified six-dimensional two-electron graph theorem. |
| Braess–Hackbusch (2005), DOI [10.1093/imanum/dri015](https://doi.org/10.1093/imanum/dri015) | Primary institutional preprint checked: approximation of \(1/x\) on \([1,\infty)\). | It is not itself the asserted \(e^{-r}\) Coulomb graph theorem. |
| Kutzelnigg (1994), DOI [10.1002/qua.560510612](https://doi.org/10.1002/qua.560510612) | Primary abstract distinguishes Hilbert-distance, energy and variance optimization; full hypotheses inaccessible. | No graph RATE inferred from its rate terminology. |
| Bachmayr–Chen–Schneider (2014), DOI [10.1007/s00211-014-0605-5](https://doi.org/10.1007/s00211-014-0605-5) | Theorem 3.2 checked in the primary preprint: \(H^1(\mathbb R^3)\) root-exponential approximation under stated Slater/transform hypotheses. | No full two-electron graph approximation. |
| Schwartz, [math-ph/0605018](https://arxiv.org/abs/math-ph/0605018), direct precursor [physics/0208004](https://arxiv.org/abs/physics/0208004) | Primary texts read: calculations with polynomial, negative-power and logarithmic terms. | Observed energy increments do not prove a graph residual lower or upper rate. |
| Erdélyi (2007), DOI [10.1016/j.aim.2006.02.003](https://doi.org/10.1016/j.aim.2006.02.003) | [Author manuscript](https://people.tamu.edu/~terdelyi/papers-online/AIM-288.pdf), Theorem 2.2, read. The separation-independent Markov inequality is used below. | It supplies the inverse estimate, not Coulomb regularity. |

The countably normed-space results motivate the hp route; they are not treated as discharged premises for (4.1).

**Why the logarithm does not refute every candidate — PROVEN (paper building block).** For any homogeneous quadratic polynomial \(P\) on \(\mathbb R^6\) and \(a>0\), \(P(x)e^{-a|x|^2}\log|x|\) admits root-exponential \(H^2\) approximation by sums of polynomial-times-Gaussians. Set
\[
\mathcal F(z)=-\tfrac12 P e^{-a|x|^2}
 \left(e^{-e^z|x|^2}-e^{-e^z}\right).
\]
Its integral on the real line equals that function by the logarithmic superposition identity. On any closed strip \(|\Im z|\le d<\pi/2\), it is \(H^2\)-valued analytic. Taylor expansion at the negative end bounds its norm by \(Ce^{\Re z}\); six-dimensional Gaussian scaling at the positive end bounds it by \(Ce^{-3\Re z/2}\). The strip trapezoidal contour estimate gives error \(Ce^{-2\pi d/h}\), and truncation at \(|j|\le N\) gives \(Ce^{-Nh}\). Taking \(h\) proportional to \(N^{-1/2}\) proves the assertion. The contour estimate follows by integrating against the cotangent kernel on the two strip boundaries; their norm integrals are finite by the displayed bounds.

This approximates one damped logarithmic term. It does not approximate the full physical eigenfunction or its angular singular structure. Thus it is not RATE, but neither is the logarithm a proof that all candidate dictionaries fail.

## 5. Theorem C proof and the data test

**Theorem C — PROVEN (paper).** Fix \(Z\ge2\) and a finite set \(\mathcal A=\{a_1,\ldots,a_J\}\subset(0,\infty)\), independent of \(n\). Let
\[
V_n^{\rm poly}
=\left\{\sum_{j=1}^Je^{-a_j(r+s)}P_j(r,s,u):
 \deg P_j\le n,\ \text{exchange-symmetric}\right\}
\]
with the singlet factor understood. Then \(V_n^{\rm poly}\subset D(H_Z)\), and there is \(c_{Z,\mathcal A}>0\) such that, for every integer \(n\ge1\),
\[
\inf_{\phi\in V_n^{\rm poly},\,\|\phi\|=1}
\|(H_Z-E_Z)\phi\|\ge c_{Z,\mathcal A}(n+1)^{-72}.
\tag{5.1}
\]
All constants below can depend on this fixed atom, exponent set, and a fixed local cube. No constant depends on the coefficients or on \(n\).

Domain membership follows by differentiating the distance polynomials away from collisions. Their weak second derivatives have at most inverse-distance singularities, locally square-integrable in transverse dimension three; the exponential controls infinity. There are no interface delta distributions.

Allowing also exchange-antisymmetric distance polynomials times triplet spinors does not evade (5.1). If a normalized fermionic trial has residual below \(\gamma/2\), its ground overlap is at least \(\sqrt3/2\); apply the following shell argument to its singlet component, whose norm is at most one. The triplet component is orthogonal to the ground and is controlled by the same spectral gap. Residuals at least \(\gamma/2\) already satisfy the stated lower bound after reducing its constant.

**Step 1: turn residual into graph error.** Let \(\psi\) be the normalized positive ground spatial function, \(\gamma=\beta_Z-E_Z>0\), and
\[
\tau=\|(H_Z-E_Z)\phi\|,\quad c_\phi=\langle\psi,\phi\rangle,\quad
\zeta=\phi-c_\phi\psi.
\]
The spectral gap gives \(\|\zeta\|\le\tau/\gamma\). Also
\(\|H_Z\zeta\|\le\tau+|E_Z|\tau/\gamma\). By (2.1),
\[
\|\zeta\|_{H^2}\le C\tau.
\tag{5.2}
\]
If \(\tau<\gamma/2\), choose the phase of \(\phi\) so that
\(c_\phi\ge\sqrt3/2\). Larger \(\tau\) already satisfies (5.1) after reducing its constant.

**Step 2: extract an actual logarithmic singularity.** The Fournais 2005 factorization, rescaled from its kinetic convention \(-\Delta\) by \(y_i=2x_i\), gives locally
\[
\psi=\exp\!\left[-Z(r+s)+u/2+
 \kappa_Z(x_1\cdot x_2)\log\rho^2\right]\Phi,
\quad \Phi\in C^{1,1},\quad
\kappa_Z=\frac{Z(2-\pi)}{3\pi}\ne0,
\tag{5.3}
\]
where \(\rho=(r^2+s^2)^{1/2}\). The additional quadratic term from \(\log4\) is absorbed into \(\Phi\). This invokes the explicit factorization, not convergence of an infinite Fock series.

Here \(\Phi(0)=\psi(0)>0\). One justification at the collision point is pointwise Feynman–Kac: for every starting point, the expectation of the time integral of each absolute Coulomb term over \([0,t]\) is at most \(C_Z\sqrt t\), since each relevant distance is a three-dimensional Gaussian projection. The potential integral is finite almost surely. The ground function is positive almost everywhere by positivity improvement, and the Brownian endpoint has a positive density. The continuous eigenfunction version of Feynman–Kac therefore has a strictly positive expectation even when started at zero.

Put \(a_*=\min\mathcal A\) and \(F=e^{a_*(r+s)}\psi\). Along \(x=\rho\omega\), \(\omega\in S^5\), differentiating (5.3) twice radially gives, almost everywhere,
\[
\partial_\rho^2F(\rho\omega)
=4\kappa_Z\psi(0)(\omega_1\cdot\omega_2)\log\rho+O(1).
\tag{5.4}
\]
The remainder is uniformly bounded on a fixed compact angular cone avoiding pair collisions. Indeed, \(\Phi_{\rho\rho}\) is bounded, \(\Phi(\rho\omega)-\Phi(0)=O(\rho)\), the degree-one factor has bounded radial derivatives, and all cross terms involving \(\rho\log\rho\) are bounded. Thus the coefficient in (5.4) cannot be canceled by the \(C^{1,1}\) remainder.

**Step 3: define bounded shell tests.** Choose a smooth nonnegative angular weight \(\chi\) supported in such a cone where \(\omega_1\cdot\omega_2>0\), with positive integral. Define
\[
\mathcal L_h(f)=
\frac{\int_{S^5}\chi(\omega)\int_h^{2h}
 \partial_\rho^2 f(\rho\omega)\rho^5\,d\rho\,d\omega}
{\int_{S^5}\chi(\omega)\int_h^{2h}\rho^5\,d\rho\,d\omega}.
\]
By (5.4), for fixed \(b_0>0,B_1\),
\[
|\mathcal L_h(F)-\mathcal L_{h^2}(F)|
\ge b_0\log(1/h)-B_1.
\tag{5.5}
\]
The normalized radial weights become identical after substituting \(\rho=ht\) and \(\rho=h^2t\); the logarithmic difference is exactly a constant multiple of \(\log h\).

Cauchy–Schwarz on a six-dimensional shell gives an \(h^{-3}\) bound for a single normalized second-derivative average. Applying it at \(h\) and \(h^2\), and differentiating the bounded radial multiplier \(e^{a_*(r+s)}\), gives
\[
|(\mathcal L_h-\mathcal L_{h^2})(e^{a_*(r+s)}\zeta)|
\le C h^{-6}\|\zeta\|_{H^2}.
\tag{5.6}
\]
Only radial derivatives of that multiplier occur; their coefficients are bounded on the fixed local region.

**Step 4: a coefficient-independent inverse estimate.** For this step use the full perimetric coordinates
\[
q_1=s+u-r,\quad q_2=r+u-s,\quad q_3=r+s-u.
\]
The physical measure becomes
\[
\frac{\pi^2}{4}(q_1+q_2)(q_1+q_3)(q_2+q_3)\,dq
\ge2\pi^2q_1q_2q_3\,dq.
\tag{5.7}
\]
On a fixed cube, rescaled to \([0,1]^3\), the function
\(Q=e^{a_*(r+s)}\phi\) is a sum of \(J\) exponential-polynomial terms
\[
Q(q)=\sum_j e^{-(a_j-a_*)(q_1+q_2+2q_3)/2}\widetilde P_j(q),
\qquad\deg\widetilde P_j\le n.
\tag{5.8}
\]
Its \(L^2(q_1q_2q_3\,dq)\) norm is bounded uniformly by normalization of \(\phi\).

The published input is Erdélyi's separation-independent exponential Markov bound on a fixed interval:
\[
\|f'\|_\infty\le C_0\left(D^2+\sum_{\nu=1}^{D}|\lambda_\nu|\right)\|f\|_\infty
\tag{5.9}
\]
for sums of \(D\) exponentials with distinct real exponents. To pass to polynomial factors, replace \(t^k e^{\lambda_jt}\) by
\[
e^{\lambda_jt}\left(\frac{e^{ht}-1}{h}\right)^k.
\]
For each fixed \(n\), take \(h\downarrow0\) sufficiently small to avoid collisions between distinct exponent blocks. The sums have at most \(D=J(n+1)\) exponents, bounded in magnitude by a fixed constant plus one, and converge in \(C^3\). Passing to the limit in (5.9) gives
\(\|f'\|_\infty\le B D^2\|f\|_\infty\), independent of coefficient cancellation. Complex coefficients are handled by taking a phase-rotated real part at a point attaining the derivative norm.

Let \(M=BD^2\ge1\). Applying this slice estimate coordinate by coordinate, and using closure under differentiation, gives
\(\|\partial^\nu Q\|_\infty\le M^{|\nu|}\|Q\|_\infty\).
At a point where \(|Q|\) reaches its maximum, a contained box of side
\(\delta=(6M)^{-1}\) has \(|Q|\ge\|Q\|_\infty/2\).
Each interval of length \(\delta\) in \([0,1]\) has \(\int t\,dt\ge\delta^2/2\). Hence
\[
\|Q\|_{L^2(q_1q_2q_3)}^2
\ge \|Q\|_\infty^2\delta^6/32.
\]
It follows that
\[
\max_{|\nu|\le3}\|\partial^\nu Q\|_\infty
\le C(n+1)^{12}\|Q\|_{L^2(q_1q_2q_3)}
\le C(n+1)^{12}.
\tag{5.10}
\]
This proves the needed inverse estimate for arbitrary fixed finite exponent sets, without bounding the individual coefficients.

Along a physical ray \(q=\rho b(\omega)\), (5.10) bounds the third radial derivative. With the matched radial weights used above, the mean value theorem therefore gives
\[
|\mathcal L_h(Q)-\mathcal L_{h^2}(Q)|\le C(n+1)^{12}h.
\tag{5.11}
\]

**Step 5: choose the two shells and conclude.** Since
\(Q=c_\phi F+e^{a_*(r+s)}\zeta\), (5.2), (5.5), (5.6) and (5.11) imply
\[
c_\phi[b_0\log(1/h)-B_1]
\le C(n+1)^{12}h+C h^{-6}\tau.
\]
Set \(h=h_0(n+1)^{-12}\), with fixed \(h_0>0\) small enough to keep both shells in the chosen cube. The first term on the right is bounded uniformly, while the logarithm on the left grows. For all sufficiently large \(n\),
\[
\tau\ge c(n+1)^{-72}\log(n+1)
\ge c'(n+1)^{-72}.
\]
For the remaining finitely many \(n\), the unit sphere of \(V_n^{\rm poly}\) is compact. Its residual minimum is positive: zero would put the ground eigenfunction in this finite space, whereas (5.5) diverges as \(h\downarrow0\) and every member satisfies (5.11) at fixed \(n\). Decrease \(c'\) to cover those finitely many orders. This proves (5.1) for all \(n\ge1\).

This direct shell proof is necessary: the bare contrapositive of a “super-algebraic approximation implies smoothness” theorem would not by itself give a uniform lower bound at every order.

In particular, (5.1) contradicts every stretched-exponential upper bound \(C e^{-cn^\alpha}\) with \(c,\alpha>0\) for this fixed dictionary, since \(n^\alpha/\log(n+1)\to\infty\).

**Consequence for the Temple loop.** For any normalized trial \(\phi\in V_n^{\rm poly}\) with \(m<\beta_Z\), let its exact ideal Temple width be \(w=v/(\beta_Z-m)\). Temple gives \(m-E_Z\le w\), and
\[
\tau^2=v+(m-E_Z)^2
\le(\beta_Z-E_Z)w+w^2.
\]
For \(w\le1\), (5.1) therefore gives
\[
w\ge c''(n+1)^{-144}.
\tag{5.12}
\]
A rational outward interval is at least as wide as this ideal interval. Width \(2^{-p}\) requires
\(n+1\ge c'''2^{p/144}\). A loop incrementing degree by one must take at least that many stages, up to an additive constant. Even perfect coefficient optimization cannot make that loop polynomial in \(p\).

**Data test — EMPIRICAL, using only existing certificates.** The input is
[width_vs_order.json](helium/remote/width_vs_order.json), SHA-256
ef752963a8ba435891966b1b6ecdf60cf5f4cdd1dbe245a5f0f0f76353930c7b.
No certificate was recomputed and no new energy digits were produced.

| Order | Existing rational width |
|---:|---:|
| 8 | \(17176011/250000000000\) |
| 10 | \(25013843/1000000000000\) |
| 14 | \(1255527/250000000000\) |
| 20 | \(83279/100000000000\) |

Ordinary least squares, using natural logarithms and the four points with equal weight, gives:

| Model for width | Fitted relation | Log-space SSE | \(R^2\) |
|---|---|---:|---:|
| Power law | \(1.61039785\,\Omega^{-4.82067881}\) | 0.00523790 | 0.99953149 |
| Exponential | \(0.00102894401\,e^{-0.36278923\Omega}\) | 0.12414262 | 0.98889590 |

The power fit has the smaller residual on these points. The fitted powers are empirical values, not certificate inputs or estimates justified by (5.12).

There are two limits on the requested falsification interpretation. First, four finite data points cannot falsify an asymptotic existential lower bound with unspecified \(c\) and \(k\); sufficiently small \(c\) accommodates any finite set of positive widths. Second, the archived trial metadata says five Decimal inverse iterations at a fixed target shift, with 90-digit Decimal precision. It does **not** certify global minimization of (2.7), even though all coefficients in the full listed subspace were active. The exact checker certifies those particular rational trials, not optimizer optimality. The data therefore do not refute (5.1), and they cannot prove it.

The entire rate calculation used the standard-library logarithm and least squares on the stored rational widths; those floating-point outputs are confined to this empirical comparison. It can be reproduced without running any moment code by taking \(y_i=\log w_i\), \(x_i=\log\Omega_i\) or \(\Omega_i\), then
\(b=\sum(x_i-\bar x)(y_i-\bar y)/\sum(x_i-\bar x)^2\),
\(a=\bar y-b\bar x\), and summing \((y_i-a-bx_i)^2\).

## 6. Status ledger with the four labels PROVEN (Lean) / PROVEN (paper) / EMPIRICAL / CONJECTURED

**PROVEN (Lean).** Source:
[AtomicTwoElectron.lean](formal/AtomicTwoElectron.lean).
Build/axiom output:
[atomic-two-electron-fixed-shift-build.log](formal/atomic-two-electron-fixed-shift-build.log).
The [reproduction log](formal/atomic-two-electron-fixed-shift-reproduction.log) records the exact command, observed toolchain, unchanged source hash and successful exit status 0.
The isolated module compiles using Lean v4.34.0-rc2 and Mathlib commit
d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9. No project-wide build or closed module is needed.

The source contains no sorry, added axiom declaration, or native_decide. The printed axiom audit uses only propext, Classical.choice and Quot.sound; the least-stopping-index statement uses no axioms. These standard logical axioms supply no Coulomb or approximation assumption.

The verified source SHA-256 is 3134f576bab8d922ddc71b64ae1fabd1fa34a46692fcf8422478754576476516. From the formal directory the isolated build command is:

~~~sh
ELAN_HOME="$PWD/.lake/tooling/elan" .lake/tooling/elan/bin/lake env lean AtomicTwoElectron.lean
~~~

Each formal statement has the following use; none asserts the continuum hypotheses:

- **initial_gap_identity_and_positive:** proves exactly the positive charge-\(Z\) arithmetic in (2.2), after the hydrogenic spectral and trial formulas have been supplied.
- **variance_quotient_of_initial_mean:** for an accepted trial with \(m\le U_Z\) and \(v\le g_Z\epsilon\), proves that its ideal Temple width is at most \(\epsilon\).
- **residual_regularized_quotient_bound:** proves (3.6), propagating a supplied residual-form defect and coefficient penalty through normalization.
- **fixed_shift_variance_quotient:** from the supplied shifted-excess identity, nonnegative mean error, shift distance at least one and spectral margin, proves the half-margin denominator and quotient bound in (2.11).
- **finite_prefix_cost_bound:** given a stage count \(n\le K(p+1)^r\), \(r\ge1\), and stage costs at most \(C(i+p+1)^k\), proves total cost at most \(CK(K+2)^k(p+1)^{r(k+1)}\).
- **least_stopping_index_le_certified:** given a decidable stopping predicate and an independently supplied successful stage \(N\), proves that its least successful index is at most \(N\).

The cost statement counts exactly \(n\) stages indexed \(0,\ldots,n-1\); a successful zero-based index \(N\) requires \(N+1\) stages. Existence of a successful physical stage is not hidden in this formalization.

**PROVEN (paper).** Kato–Rellich domain and graph equivalence; the rank-one separator and simple ground state for every fixed \(Z\ge2\); continuum Temple including rational outward endpoints; the counterexamples to unrestricted variance selection; corrected fixed-shift selection and rate-free core termination; the conditional cost composition under explicitly added effective dictionary hypotheses; finite hp domain membership and moment computability; Theorem C including finite fixed exponent sets; the single Gaussian-damped logarithm approximation. These are human proofs using the stated analytic theorems, not machine proofs of a Coulomb solver.

**EMPIRICAL.** Only the least-squares comparison of the archived order-8, 10, 14, 20 widths. The archived certificate endpoints remain exact rational arithmetic results subject to their existing paper analytic inputs; global optimality of their coefficient selection is not certified.

**CONJECTURED.** Theorem T; the atomic graph RATE for an augmented or geometrically refined dictionary; LPWA (4.4). The uncompleted hp approximation and computational transfers are identified in §4, not relabeled as proven because they have plausible constructions. The general statement “RATE as written implies the prescribed loop and its polynomial cost” is refuted as an abstract implication, not labeled a conjecture.

## 7. What a human reviewer must check, ranked

1. **Theorem C's logarithmic term and shell argument.** Check the kinetic rescaling in (5.3), strict positivity at the triple collision, the uniform bounded remainder in (5.4), the \(H^2\)-bounded shell functionals, and the passage from fixed finite-order compactness to the all-order lower bound. These are the analytic claims most directly responsible for (5.1).
2. **The finite-exponent inverse estimate.** Check the exact hypotheses of Erdélyi's Theorem 2.2, the confluent limit, and the weighted peak-box argument, especially cancellation independence. A coefficient-dependent bound would not prove Theorem C as stated.
3. **The actual optimization objective.** Check (2.7)–(2.8) before accepting any assertion that a variance-minimizing pencil selects the ground branch. The modified objective (2.9) and additive tolerances must be used explicitly in any continuation.
4. **The distinction between computability and polynomial cost.** Supply an explicit generator, integer/parameter bounds, a polynomial moment algorithm, and a regularization witness bound for the selected dictionary before applying (3.5). Existential approximation constants need not be made explicit.
5. **The local-to-global hp transfer.** Prove or refute LPWA for the reduced physical operator; then verify the weighted graph interpolation, exterior/tail construction and quadrature complexity. Ordinary uniformly elliptic polyhedral theorems do not discharge these merely because the coordinate domain is an octant.
6. **Formal scope and data provenance.** Rebuild only the linked atomic module, inspect every stated hypothesis and axiom audit, and reproduce the fit from the four archived rational widths. Do not confuse scalar Lean proofs with the continuum analytic inputs, or those trial certificates with certificates of optimizer optimality.

The next precise local question is whether LPWA (4.4) holds for the actual positive ground state of every fixed two-electron atom with \(Z\ge2\). A positive answer would address the vertex regularity break; Theorem T would still require the corrected loop and the remaining explicit approximation and cost transfers.
