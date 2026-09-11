> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Independent audit of the global dyadic construction

**PROVEN — paper audit of the stated implication.** The global proof
passes the checks below. Its physical inputs G1--G3 have separate
proofs; no numerical convergence result or Lean verification is used.
The rate concerns the actual six-dimensional physical \(H^2\) norm.

## 1. Exterior analytic input

The statement and proof through (E2) in
EXTERIOR_ANALYTIC_ATTEMPT.md were independently checked.

The bounded-drift conjugation is exact. In its Moser calculation the
unabsorbed gradient coefficient is \(4(p-1)/p^2\). Absorbing one
quarter in each cross term gives gradient-cutoff coefficient
\(2p^2/(p-1)^2\le8\), drift coefficient
\(B^2p^2/[2(p-1)^2]\le2B^2\), and potential coefficient
\(C_0p^2/[2(p-1)]\le pC_0\). These verify (E4).
The Sobolev constant three is sufficient, and the iteration product
is smaller than \(2^{18}K_Z^{3/2}\). Thus the stated global amplitude
bound is supported by the calculation, rather than an invalid
six-dimensional \(H^2\)-to-\(L^\infty\) embedding.

The physically rescaled nuclear KS coefficient (E6) has the correct
powers \(-8hZ\), \(8h^2|y|^2W\), and
\(-8h^2E_Z|y|^2\). Its coefficient bounds are uniform over exterior
centers because the spectator distances have fixed positive lower
bounds. A single fixed small \(h\) permits the same oscillator
estimate and factorial initialization as in the RWA proof.

The distance-coordinate estimates were checked directly:
\[
 |\Delta z|\le9\delta,\qquad
 |\Delta w|\le20S\delta+82\delta^2
             \le102(1+S)\delta.
\]
The choice \(c_0\le h_*^2/2^{20}\) in a radius
\(c_0/(1+S)\) preserves both the invariant-series domain near
collinearity and the positive square-root branch away from it.
The pair-axis coordinate maps instead have fixed radii; large
spectator factors cancel against their denominators. Consequently
(E1) has the asserted polynomial radius loss and common amplitude.
No compactness of an unbounded exterior set is assumed.

After rescaling, this gives shell radius at least
\(c(1+\tau)^{-2}\). Combined with the direct vertex estimate in the
RWA proof, the normalized functions
\(\tau^{-\sigma}[\widehat\psi(\tau\cdot)-\psi_0]\)
have a common analytic amplitude for all positive shell scales.
The more conservative constants used in the global construction
are therefore legitimate.

## 2. Polynomial approximation and its dependence on the outer radius

For a common normalized analytic radius \(h\), the global proof uses
at most \(N=O(h^{-3})\) cutoff boxes. Leibniz's formula for a product
of at most \(N\) Gevrey-2 cutoffs gives derivative scale \(O(N/h)\);
undifferentiated factors are at most one. Thus it does not introduce
a constant exponential in \(N\). Summing the box contributions gives
\[
 M_0=O(h^{-3}),\qquad B_0=O(h^{-4}).
\]
The cosine/Fourier calculation has decay parameter \(b_0h^2\).
Counting frequency triples and two derivatives costs the tail
\(\sum_{N>d}(N+1)^6e^{-b_0h^2\sqrt N}\).
After reserving half the exponential, the integral substitution
\(t=\sqrt N\) has degree thirteen; the inverse decay-parameter power
is fourteen. Multiplying by \(M_0\) gives \(h^{-31}\).
With \(h\asymp(1+T)^{-2}\), these are exactly the prefactor
\((1+T)^{62}\) and rate parameter \((1+T)^{-4}\) in (G7).

The Chebyshev coefficient-sum estimate also bounds the same
polynomials on the whole containing cube. Outside it their
derivatives grow at most polynomially as
\((q+1)^4(6t)^q\). This is the required estimate on the actual
polynomials; no compactly supported surrogate is substituted into
the witness.

## 3. Telescoping, constant cancellation, and exact dictionary index

Writing \(f=\psi-\psi_0\), direct expansion verifies
\[
 \psi-v_q=
 \psi(1-E_{\rm out})+fE_{\rm in}
 +\sum_{j=j_0}^J W_{j,p}(f-P_j).
\]
The use of \(\psi_0E_{\rm out}\) at the same outer node is essential.
It makes the omitted exterior function \(\psi\), which has a
physical tail, while the inner omitted function is \(f\), which
vanishes at the triple point.

Every term has one of the original nodes \(Z2^j\), including the
adjacent node \(j+1\), and degree at most \(p+q\). Therefore
\[
 p+q+2(J+1)=769q+770
 \quad\text{when}\quad p=J=256(q+1).
\]
The term at the outer node has degree only \(p\), so it obeys the
same budget. Distance-polynomial times decaying-exponential terms
are globally in physical \(H^2\); their inverse-distance Hessians
are square integrable. Exchange symmetry is preserved.

## 4. Shell tails and all physical powers

The fitted-shell scaling must retain
\(\tau^{\sigma+1}(1+\tau^2)\). Its two summands cover the physical
second-derivative and zero-order scales; the first-order scale lies
between them. This factor is present in (G15)--(G18).

For the upper tail \(t=S/\tau\ge2\), the target contribution before
physical integration is bounded at order zero by
\[
 C\tau^\sigma(p+1)^3(1+T)^4
 t^{\sigma+7}e^{-pI(t)}.
\]
Its squared six-dimensional volume factor has power
\(t^{2\sigma+19}\), smaller than \(t^{21}\) because \(\sigma<1\).
The polynomial contribution has only \(t^{11}(6t)^{2q}\) before
the same exponential. Higher derivative and inverse-distance terms
have no worse power. Thus the intentionally conservative envelope
in (G16) is valid, including the physical angular integrals.

The remaining integral is exactly
\[
 \int_2^\infty t^{21}(t/2)^{2q-2p}\,dt
 =\frac{2^{22}}{2p-2q-22}.
\]
With \(p=256(q+1)\), the factor
\(12^qe^{-p/4}\) after taking the square root is bounded by
\(Ce^{-p/16}\), using \(\log12<3\).

On the lower tail, \((4t)^{p/2}\) compensates the derivative powers
at zero. Its apparent \(4^p\) cancels upon integration up to
\(t=1/4\); there is no hidden exponential prefactor. All constants
can be chosen independently of the shell number.

The geometric sum
\[
 \sum_j\tau_j^{\sigma+1}(1+\tau_j^2)
 \le C_\sigma(T^{\sigma+1}+T^{\sigma+3})
 \le C_\sigma(1+T)^4
\]
therefore gives (G19), without a factor depending on the number of
shrinking shells.

## 5. Inner and outer omissions

For the inner term, the amplitude vanishing in G1 gives the physical
scale \(\tau_*^{\sigma+1}\). On \(t\ge2\) the gamma density decreases
at logarithmic derivative at most \(-1/2\), so
\(E_p(pt)\le2e^{-pI(t)}\); its derivatives have only polynomial
factors. The global two-derivative envelope G5 pays for the part
outside the vertex neighborhood. This verifies (G20).

For the outer term, (G21) follows from the gamma density on
\(S/\tau_0<1/4\); the residual lower-tail power removes the apparent
inverse powers at zero. Global Hardy bounds control the
\(\psi/r,\psi/s\) terms on this inner portion of the outer error.

On \(S\ge T/8\), the cutoff used in Hardy is only an estimate tool.
It is not part of \(v_q\). With
\(\chi=0\) below \(T/16\) and \(\chi=1\) above \(T/8\),
\[
 \|\psi/r\|_{L^2(S\ge T/8)}
 \le2\|\nabla_{x_1}(\chi\psi)\|_2
 \le C(1+T^{-1})\|\psi\|_{H^1(S>T/16)}.
\]
Together with \(|g'|\le p/\tau_0\) and
\(|g''|\le2p^2/\tau_0^2\), this proves the physical \(H^2\) product
estimate in (G23). No derivative of a sharp region indicator is
taken. A physical tail estimate alone would not justify dropping
these inverse-distance terms; the localized Hardy step correctly
supplies them.

## 6. Rate and audit conclusion

For \(T=(q+1)^{1/16}\),
\[
 \sqrt q/(1+T)^4\ge c q^{1/4}.
\]
The slowest exponential in (G24) is consequently the physical
outer tail \(e^{-cq^{1/16}}\). Its polynomial prefactor is absorbed
by decreasing \(c\); finitely many small indices can be handled by
enlarging the fixed constant. Thresholds such as \(T/16\ge1\) may
be large but are fixed, and no claim of practical efficiency is
made from these asymptotic constants.

The explicit Coulomb graph bound (G26) follows from the trace
estimate for the Laplacian and sliced Hardy. The \(L^2\) approximation
eventually makes the witness norm at least \(1/2\), so normalization
preserves the rate and gives the residual for the actual continuum
ground-state energy.

**Audit conclusion:** the regularity-to-global-RATE implication in
GLOBAL_DYADIC_ATTEMPT.md is proved by the displayed construction.
Its G1 and G2 inputs are discharged by the separately audited
vertex and exterior analytic proofs; G3 is the previously proved
physical domain and exponential-tail result. This establishes one
admissible global witness with a controlled exterior, rather than
only a collection of unrelated local approximants.

The finite-dimensional optimization, rounding schedules, and
bit-complexity composition remain separate obligations and were
not audited in this file.
