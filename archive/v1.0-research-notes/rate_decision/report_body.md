> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Which RATE lemma should we try to prove next?

Decision experiment, 9 September 2026. This report concerns the atomic two-electron problem in `TWO_ELECTRON_THEOREM.md`. Theorem T remains **OPEN**. No new continuum approximation theorem or Lean theorem is claimed.

## Fixed problem, objective, and status conventions

All numerical experiments use helium, (Z=2), with the unrestricted operator

\[
H=-\tfrac12(\Delta_1+\Delta_2)-2/r-2/s+1/u,
\quad r=|x_1|, s=|x_2|, u=|x_1-x_2|.
\]

The spatial functions below are symmetric under (r\leftrightarrow s); multiplication by the normalized antisymmetric spin singlet gives fermionic trials in (D(H)=H^2(\mathbb R^6;\mathbb C^4)\cap\mathcal H_-). The scalar products omit their common angular constant only. Every reported (Q_{ij}) is ⟨Hφ_i,Hφ_j⟩ for the continuum action, not the square of a projected Hamiltonian.

**PROVEN (existing paper):** the prior report supplies (L=-4, U=-11/4, \beta=-5/2), the operator-domain facts for ordinary distance polynomials and conforming hp lifts, and the continuum Temple argument. Its Theorem C rules out the requested fast asymptotic graph rate for every *fixed finite* positive exponential set with nonnegative distance powers. The precise exponent 72 in that obstruction is not a fitted exponent.

Selection uses only the corrected fixed shift \(\sigma=-5\):

\[
J_\tau(c)=\frac{c^T(Q+10A+25G+\tau I)c}{c^TGc},\qquad \tau>0.
\]

The equivalent reciprocal maximization is used where numerically more stable. Candidate coefficients are rationalized before certification. The acceptance test is \(m=\langle H\rangle\le-11/4\). A near-eigenvalue shift and global variance optimization are absent. Published helium digits, where present in exploratory diagnostics, are not selection, acceptance, or certificate inputs.

**EMPIRICAL** means finite arithmetic screening, fits, timing, or a scientific judgment about the next proof target. **PROVEN (this session)** means the elementary finite calculations explained here or the exact rational interval certificate checked by Python; it does not mean Lean verified. **OPEN** marks missing analytic/effective bounds. **REFUTED** is reserved for an actual obstruction, not an unsuccessful pilot.

## Phase 0: exact dictionaries and the domain/certification gate

Let \(\mathcal P_d\) be the symmetric nonnegative-power distance polynomials of total degree at most \(d\), with \(\mathcal P_d=\{0\}\) for \(d<0\). A generator is
\[
P_{ihk}=\frac{(r^is^h+r^hs^i)u^k}{(i+h+k)!},\quad i\ge h\ge0, i+h+k\le d,
\]
using one copy rather than two when \(i=h\). Define \(a_d=\dim\mathcal P_d\). For \(d=2q,2q+1\), respectively,
\[
a_{2q}=\frac{(q+1)(q+2)(4q+3)}6,qquad
a_{2q+1}=\frac{(q+1)(q+2)(4q+9)}6.
\]

| Candidate | Exact dictionary | Domain | Moments and implementation | Size / parameter heights | Obstruction / effort |
|---|---|---|---|---|---|
| A, control | \(e^{-2(r+s)}\mathcal P_n\) | **PROVEN (existing paper)** | Existing exact (G,A\in\mathbb Q), (Q\in\mathbb Q+\mathbb Q\log2+\mathbb Q\pi^2\); fixed-shift driver added | (a_n=O(n^3)); polynomial rational heights | Fast RATE **REFUTED** by Theorem C; minimal implementation |
| B, quadratic Fock log | \(e^{-2(r+s)}[\mathcal P_n+q\log R\,\mathcal P_{n-2}]\), (q=(r^2+s^2-u^2)/2, R=r^2+s^2\) | **PROVEN (this session)**, elementary check below | Finite radial log moments and one-dimensional angular integrals; new screening evaluator | (a_n+a_{n-2}=O(n^3)); fixed rational parameters | Physical full-eigenfunction approximation and conditioning **OPEN**; medium new moment work |
| C, Schwartz F | \(e^{-S}S^\ell(U/S)^m(T/S)^{2j}(\log S)^h\), (h=0,1, \ell,m,j\ge0, \ell+m+2j\le n\), (S=r+s,T=r-s,U=u\) | **PROVEN (this session)**, including degree-zero logarithms | Exact angular recurrence with radial log moments in a larger explicit constant algebra; screening/certification extension | (2\sum_{j=0}^{\lfloor n/2\rfloor}\binom{n-2j+2}{2}=O(n^3)); polynomial rational generator heights | Physical graph RATE and quantitative Gram control **OPEN**; medium extension |
| D, full tensor hp | Defined precisely below on dyadic tensor cells; globally (C^1\), degree (p_n=3+\lfloor n/3\rfloor^2\) | **PROVEN (existing paper)**, applied to the explicit generator | Rational (G,A\); rational-integrand (Q\); implemented Duffy screening, explicit rational quadrature route | (O(n^9)\); polynomial knot/basis heights | LPWA, graph interpolation and exterior/tail bridge **OPEN**; highest implementation effort |
| E, expanding exponents | \(\sum_{j=0}^{\lfloor n/2\rfloor}e^{-2^{j+1}(r+s)}\mathcal P_{n-2j}\) | **PROVEN (existing paper)** applied termwise | Existing moment field unchanged; complete exact/interval implementation | \(\sum_j a_{n-2j}=O(n^4)\); largest exponent bit length \(\lfloor n/2\rfloor+2\) | Theorem C does not cover an expanding set; direct graph approximation **OPEN**; small exact-code extension |

Here is the exact D generator. On each axis take breakpoints \(\{0\}\cup\{2^j:-n\le j\le n+1\}\), endpoint knot multiplicity \(p_n+1\), and interior multiplicity \(p_n-1\). Use the resulting rational B-splines of degree \(p_n\), deleting the last two functions so that value and first derivative vanish at the outer endpoint. Extend by zero. Take the tensor products and retain one symmetric (a,b) combination per exchange orbit. No boundary value is prescribed on a physical octant face. The spaces are nested by knot insertion, degree elevation, and extension of the outer zero region. There are (O(n^3)) one-dimensional generators and (O(n^9)) tensor generators. The measured dimensions are actual independent B-spline dimensions, not merely a count of redundant columns.

To obtain a cheaper but explicitly distinct hp trend, we also screen **D-shell**: compact (C^1) radial splines in \(t=a+b+c\), degree (n+3\), breakpoints \(\{0\}\cup\{2^j:-n\le j\le n+2\}\), multiplied by \(c^j(a-b)^{2k}\) with (j+2k\le n\). This is a genuine conforming piecewise-polynomial family on simplex shells, of size (O(n^4)\). It is not the tensor family and is not substituted for it in a RATE claim.

**PROVEN (this session), finite domain checks.** For B, (q=O(\rho^2)\), (R\asymp\rho^2\) in six spatial dimensions, so derivatives of (q\log R\) of orders 0,1,2 have orders (\rho^2\log\rho,\rho\log\rho,1+|\log\rho|\). Their relevant squares are locally integrable. Distance cusps introduce at most inverse pair distances in the Hessian, square integrable in transverse dimension three. Exponential decay controls infinity. Products and finite sums retain (H^2\), and Hardy controls Coulomb multiplication. For C, each generator is homogeneous of degree \(\ell\) times a bounded angular function and at most one radial logarithm. The (S\) denominator vanishes only at the six-dimensional origin; two derivatives there have radial size \(\rho^{\ell-2}(1+|\log\rho|)\), whose squared radial integral is bounded by a constant times \(\int_0^1\rho^{2\ell+1}(1+|\log\rho|)^2d\rho<\infty\). At nonzero pair collisions only the usual distance-cusp factors occur. Standard shrinking-boundary integration by parts gives these derivatives distributionally; it introduces no point or interface delta. Thus even the \(\ell=0\), (\log S\) functions are admissible. No silently removed terms are needed for domain membership.

The C indexing and decay are those of Schwartz, equation (0.3), [math-ph/0605018](https://arxiv.org/abs/math-ph/0605018): its (k=2\) means (e^{-S}\), not (e^{-2S}\). The entire displayed dictionary is used. The earlier [physics/0208004](https://arxiv.org/abs/physics/0208004) low-log omissions are not silently mixed into this definition. B uses the actual quadratic scalar product in the Fournais factor, [math-ph/0312060](https://arxiv.org/abs/math-ph/0312060), DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6). Depth two is not run: (H^2\)-admissibility of its square is easy, but a verified nonzero *physical* quartic log-square coefficient was not established by the available (C^{1,1}\) factorization. That factorization permits cancellation by the remainder.

No family fails the finite domain gate. The analytic RATE is open for B–E. Where a certifier is not implemented, cheap screening is explicitly separated from a certified result; the concrete moment routes below explain why screening is meaningful, and no expensive certificate run is based on an unspecified integral oracle.

## Moment classes and certification obligations

**PROVEN (existing paper), instantiated this session:** for A/E, mixed exponent products use \(\kappa=\alpha_i+\alpha_j>0\). All required integrals are
\[
M_{abc}(\kappa)=\int_{|r-s|\le u\le r+s}e^{-\kappa(r+s)}r^as^bu^c\,dr\,ds\,du,
\quad a,b,c\ge-1, a+b+c>-3.
\]
The radial factor is \((a+b+c+2)!/\kappa^{a+b+c+3}\); the angular recurrence is unchanged. With its powers of two included, the full field remains \(\mathbb Q+\mathbb Q\log2+\mathbb Q\pi^2\). Both exponent-dependent (H\)-actions are evaluated before taking a mixed inner product.

For C the extension is
\[
\int_\triangle e^{-\kappa S}r^as^bu^cS^d(\log S)^h\,dr\,ds\,du,
\qquad h\le2.
\]
After the same angular integration, let \(\nu=a+b+c+d+2\ge1\). The three radial factors are
\[
R_{\nu,0}=\nu!/\kappa^{\nu+1},\quad
R_{\nu,1}=R_{\nu,0}(H_\nu-\gamma-\log\kappa),
\]
\[
R_{\nu,2}=R_{\nu,0}[(H_\nu-\gamma-\log\kappa)^2+\pi^2/6-H_\nu^{(2)}].
\]
For this dictionary \(\kappa=2\), yielding the algebra \(\mathbb Q[\gamma,\log2,\pi^2]\), with bounded logarithmic degree. This is larger than the old three-component vector field. One can alternatively bound the base radial log integrals directly and generate higher moments by integration by parts. For example, \(\gamma=-\int_0^\infty e^{-t}\log t\,dt\). On \([0,T]\), integrate the Taylor polynomial of (e^{-t}\) exactly against \(\log t\); each term is \(T^{k+1}[\log T/(k+1)-1/(k+1)^2]\). A remainder bound is
\[
\frac{T^{K+2}(\log T/(K+2)-1/(K+2)^2)+2/(K+2)^2}{(K+1)!},
\]
and for (T\ge1\) the tail is at most \((T+1)2^{-T}\). Dyadic (T=O(p)\) and sufficiently large (K=O(p)\) give a rational (p\)-bit route without using a floating gamma value as a certificate.

For B the new class is
\[
\int_\triangle e^{-4(r+s)}r^as^bu^c(r^2+s^2)^{-d}
[\log(r^2+s^2)]^h\,dr\,ds\,du.
\]
Set \(S=r+s, t=|r-s|/S\). Then \(R=S^2(1+t^2)/2\); the radial part uses positive-integer gamma derivatives and the remaining one-dimensional angular part contains rational factors, \(\log((1+t^2)/2)\), and possibly \(-\log t\). Endpoint cancellations must be grouped before bounding. This is a direct certified quadrature problem, not an assertion that the old moment field suffices. A finite quadrature extension is distinct from the still-open polynomial conditioning and physical RATE theorem.

For D, with \(w=(a+b)(a+c)(b+c)\), cellwise (H\phi_i=P_i/w\), hence
\[
Q_{ij}=\int_{\rm cell}\frac{P_iP_j}{w}\,da\,db\,dc.
\]
On an origin cube split into six coordinate orderings. On one sector (a=h\rho,b=h\rho t,c=h\rho tv\), the denominator and Jacobian give \([\rho(1+t)(1+v)(1+tv)]^{-1}\). Since each (P_i\) vanishes to order at least two, the radial singularity cancels. Axis cells use a two-dimensional Duffy map. Remaining denominators are separated from zero on each rescaled geometric cell. Expand each reciprocal about a rational midpoint: if \(|1-D/D_0|\le1/2\), the geometric tail after (K\) terms is at most \(2^{1-K}/D_0\). The retained polynomial integrates rationally. This gives a specific constant-tracking route; a complete global generator/quadrature bit bound is **OPEN**, not inferred merely from computability.

{{SCREENING}}

{{CERTIFICATES}}

{{DIAGNOSTICS}}

{{DECISION}}
