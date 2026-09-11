> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Dyadic RATE proof attempt

**Stop condition B: the physical leading-singularity rate is PROVEN; the
global ground-state graph RATE remains OPEN.** The construction uses
exactly the prescribed dictionary and obtains an exponential local bound.
It does not promote a local component estimate into a ground-state
algorithm. All new mathematical results below are **paper proofs**.
There are no new Lean theorems, numerical RATE experiments, or energy
certificates in this session.

For every fixed integer \(Z\ge2\), keep
\[
H_Z=-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u,\qquad
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
e^{-Z2^j(r+s)}\mathcal P_{n-2j}^{\mathrm{sym}}.
\]
Spatial functions are tensored with the normalized spin singlet. The
physical domain is \(H^2\cap L^2_{\mathrm{sym}}\), with the established
Kato–Rellich operator; \(\psi_Z\) is its normalized positive ground state.
The norm used for the proof is
\[
\|v\|_{H^2_*}^2=\|v\|_2^2+\|\nabla v\|_2^2+\|D^2v\|_{F,2}^2.
\]
It counts every Cartesian second derivative and dominates the usual
\(H^2\) norm. None of the arguments replaces it by an energy or \(H^1\)
norm.

## 1. The leading physical singularity is approximated

Let
\[
S=r+s,\quad \rho^2=r^2+s^2,\quad
q=x_1\cdot x_2=(r^2+s^2-u^2)/2,\quad
\kappa_Z=\frac{Z(2-\pi)}{3\pi}.
\]
The verified local factorization yields the exact extraction
\[
\psi_Z=
\underbrace{\kappa_Z\psi_Z(0)e^{-ZS+u/2}q\log\rho^2}_{f_{\log,Z}}
+e^{-ZS+u/2}\mathcal R_Z,\qquad
\mathcal R_Z\in C^{1,1}_{\rm loc}.
\tag{1}
\]
In addition, \(\mathcal R_Z(0)=\psi_Z(0)\),
\(\mathcal R_Z-\psi_Z(0)=O(\rho^2)\), and \(D\mathcal R_Z=O(\rho)\).
This follows from Fournais et al., Theorem 1.1,
[math-ph/0312060](https://arxiv.org/pdf/math-ph/0312060),
DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6),
with the actual kinetic rescaling \(y_i=2x_i\).
The derivation and hypotheses are checked in
[the physical audit](dyadic_proof/PHYSICAL_REGULARITY_AUDIT.md).

**PROVEN — physical leading-singularity theorem.** For every sufficiently
small fixed \(0<D\le1/\sqrt2\), there are explicitly specified
\(g_n\in V_n^{(Z)}\subset D(H_Z)\), for all \(n\ge0\), satisfying
\[
\boxed{\|f_{\log,Z}-g_n\|_{H^2_*(B_D)}
\le C_{\log}(Z,D)\,2^{-n/104}.}
\tag{2}
\]
The constant is fully displayed in (L4)–(L5) of
[LEADING_SINGULARITY_THEOREM.md](dyadic_proof/LEADING_SINGULARITY_THEOREM.md).
It includes the fixed physical amplitude \(|\kappa_Z\psi_Z(0)|\).
That file contains the complete composition proof and exact witness.
Its local graph and shifted-operator conclusions are (L6)–(L7), on
\(B_{D/2}\).

Here is the mechanism, with the dictionary accounting made explicit.

First, the actual identity
\[
\log\rho= \log S+\log(\rho/S),\qquad
\log(\rho/S)=-\tfrac12\sum_{k\ge1}(2rs/S^2)^k/k
\tag{3}
\]
retains the angular dependence. The ratio \(2rs/S^2\) is at most \(1/2\).
Cartesian differentiation, including the apparent \(1/r\) and \(1/s\)
Hessian terms, shows geometric convergence of this series in physical
\(H^2_*\) after multiplication by \(qe^{-ZS}\).
The factor \(|q|\le rs\) controls the pair-axis terms.

Second, every retained inverse power is eliminated through
\[
e^{-ZS}S^{-2k}=\frac1{(2k-1)!}
\int_Z^\infty(\lambda-Z)^{2k-1}e^{-\lambda S}\,d\lambda.
\tag{4}
\]
Use \(I_0=[Z,3Z/2]\) and
\(I_j=[3Z2^j/4,3Z2^j/2]\) for \(j\ge1\).
Taylor expansion is about exactly \(Z2^j\). Banach-valued Cauchy estimates
in the right half-plane control both physical derivatives and increasing
angular order. All final terms have the form
\[
e^{-Z2^jS}q(rs)^kS^b.
\]
Their consumed dictionary index is \(2+2k+b+2j\).
Retaining \(K=m\) angular terms, Taylor degree \(P=16m\), and node index
\(J=4m\) consumes \(26m+2\). The coefficients are rational polynomial
integrals. The proof estimates angular truncation, finite-panel Taylor
error, and the omitted Laplace tail separately.
It gives global \(H^2_*\) error \(C_Z2^{-n/52}\) for the angular component.
See [ANGULAR_LEMMA.md](dyadic_proof/ANGULAR_LEMMA.md).

Third, Frullani's logarithm integral, with its singular head cancellation
retained, is expanded over the same admissible scales for the radial
component \(qe^{-ZS}\log S\). With \(J=\lfloor n/4\rfloor\) and
\(p=n-2J-2\), its error is bounded by
\[
Z^{-3}\left[3200(n+4)^5\,2^{-n/2}+12000\,2^{-3n/4}\right]
\quad(n\ge4).
\tag{5}
\]
The final terms are \(e^{-Z2^jS}qS^k\), of degree \(k+2\le n-2j\).
See [DYADIC_RADIAL_LEMMA.md](dyadic_proof/DYADIC_RADIAL_LEMMA.md).
Adding the radial and angular witnesses gives a global \(H^2_*\)
approximation of \(qe^{-ZS}\log\rho^2\) at rate \(2^{-n/52}\).

Finally, multiply that witness at index \(N=\lfloor n/2\rfloor\) by
\[
T_L(u)=\sum_{\ell=0}^{L}(u/2)^\ell/\ell!,\qquad L=\lceil n/2\rceil.
\]
The index is \(N+L=n\). On \(B_D\), multiplication by \(T_L\) has
uniform physical \(H^2_*\) bound \(5e^{D/\sqrt2}\), using sliced Hardy
for its \(1/u\) Hessian. The omitted exponential series has factorial
error through derivative order two. This proves (2), including the
physical cusp multiplier. The witness has no logarithmic, negative-power,
cutoff, or freely located exponential basis functions.

The independently audited constants are deliberately conservative.
Equation (2) proves \(\alpha=1\) for this local component only; it does
not predict the exponent for the full eigenfunction.

## 2. Pair collisions: fixed patches close, uniform simultaneous approximation does not

**PROVEN — actual isolated-pair structure.** Fournais et al., Theorem 1.4,
[0806.1004](https://arxiv.org/pdf/0806.1004),
DOI [10.1007/s00220-008-0664-5](https://doi.org/10.1007/s00220-008-0664-5),
applies because \(\psi_Z\in H^2\subset W^{1,2}_{\rm loc}\) solves the
physical equation. It gives \(\psi_Z=A+rB\) near an isolated \(r=0\)
collision, and the corresponding \(s\) and \(u\) decompositions with
Cartesian analytic coefficients. Its neighborhoods exclude simultaneous
collisions.

The physical audit proves that rotation invariance converts these
decompositions to analytic functions of the ordinary distances on each
fixed isolated-pair patch. For example, near \(r=0,\ s=s_0>0\), rotate
\(x_2\) to \(se_3\) and substitute
\[
z=\frac{r^2+s^2-u^2}{2s},\qquad |x_{1,\perp}|^2=r^2-z^2.
\]
The denominator is harmless on this fixed patch. Exchange-invariant
Taylor polynomials in \(S,(r-s)^2,u\), of auxiliary degree \(k\), have
ordinary distance degree at most \(2k\). After the \(e^{-ZS}\) factor,
they belong to \(V_{2k}^{(Z)}\) and approximate on a smaller patch at
exponential rate in physical \(H^2_*\). The proof includes the
square-integrable \(1/r,1/s,1/u\) Hessian terms. Corresponding relative
coordinates handle \(u=0\). These are separate local existence statements,
not a single approximation to the whole state.

The overlaps can be located exactly. For \(0<\eta<1/3\), the cones
\[
r<\eta S,\qquad s<\eta S,\qquad u<\eta S
\tag{6}
\]
and their relative closures are pairwise disjoint for \(S>0\).
For example, \(r,u\le\eta S\) implies
\(S=r+s\le2r+u\le3\eta S<S\).
Outside these cones all three distances are at least \(\eta S\).
However, each cone meets every sufficiently small triple-collision ball
at arbitrarily small positive \(S\). The constants in the isolated-pair
charts are not quantified uniformly on those shrinking intersections.
The leading-log proof does cover its own pair-axis contributions there;
it does not cover the nonconstant physical remainder there.

**OPEN:** simultaneous scale-uniform approximation of the actual pair
structures by one member of \(V_n^{(Z)}\). The missing physical information
is the derivative bound in Section 3. Separately, even local estimates with
that information would need a global realization in this dictionary.
Multiplying independent local polynomials by a partition of unity would
introduce functions outside \(V_n^{(Z)}\).

## 3. The smallest next physical obstacle

The \(C^{1,1}\) conclusion in (1) supplies bounded second Cartesian
derivatives. The isolated-pair theorem supplies analytic charts away from
the triple point. Neither verified source supplies factorial derivative
constants uniform as those charts approach the point. Existence of each
chart is not a lower bound for its rescaled analyticity radius.
No representation by an all-order physical Fock series is used.

Here is the one next physical lemma, with the remainder already extracted.
Use half-perimetric coordinates
\[
r=b+c,\qquad s=a+c,\qquad u=a+b,\qquad S=a+b+2c,
\]
and let \(\widehat{\mathcal R}_Z(a,b,c)\) be the rotationally reduced
remainder from (1), well-defined on the closed octant.

**OPEN — uniform weighted analyticity of the extracted remainder.**
For every fixed integer \(Z\ge2\), do there exist
\(\delta,A,C>0\) and \(0<\sigma<1\) such that for every
\(\nu\in\mathbb N_0^3\) and every \((a,b,c)\in[0,\infty)^3\) with
\(0<S<\delta\),
\[
\boxed{
\left|\partial^\nu
\bigl(\widehat{\mathcal R}_Z-\psi_Z(0)\bigr)(a,b,c)\right|
\le C A^{|\nu|}|\nu|!\,S^{\sigma-|\nu|}?
}
\tag{7}
\]
Derivatives at nonvertex boundary points mean those of the local real
analytic extensions proved by the invariant-coordinate argument.
Their qualitative existence is already established; the single missing
assertion in (7) is the uniform inequality over all orders and scales.
The constants may depend on fixed \(Z\), never on \(\nu\) or the point.
The weak range \(0<\sigma<1\) avoids requiring more vertex vanishing than
the next analytic step needs; the already established quadratic
vanishing remains valid.

This statement concerns derivatives of an identified physical function;
it does not rephrase the desired dictionary RATE. A proof of (7) would
address the first physical gap. It would still leave the distinct
approximation question of how to join angular/pair pieces using only
the prescribed exponential blocks, and the exterior matching below.
Those are not hidden in the word “regularity.”

## 4. The physical exterior tail is bounded; the dictionary exterior remains open

**PROVEN — physical tail.** A direct proof gives
\[
\|e^{(Z/4)\rho}\psi_Z\|_2^2
\le\frac{161\,3^{32}}{159},
\qquad
\|\psi_Z\|_{H^2_*(\rho>T)}
\le C_{\mathrm{tail},Z}e^{-ZT/4}\quad(T\ge0).
\tag{8}
\]
Every constant in \(C_{\mathrm{tail},Z}\) is given in
[EXTERIOR_CONSTANTS.md](dyadic_proof/EXTERIOR_CONSTANTS.md), (X1).

The elementary proof in the physical audit uses the IMS partition
\(r/\rho,s/\rho\) and the hydrogenic lower bound to obtain, for functions
vanishing inside \(\rho<R\),
\[
\mathfrak h_Z[f]\ge
\left[-Z^2/2-\frac{3Z}{2R}-\frac1{2R^2}\right]\|f\|^2.
\]
The established upper bound \(E_Z\le-Z^2+5Z/8\) yields an ionization
margin at least \(3Z^2/16\). A truncated exponential weight with
\(a=Z/4,\ R_0=32/Z\) proves the weighted \(L^2\) estimate. Hardy and the
weighted eigenfunction identity give weighted first derivatives. A smooth
exponential weight and the actual domain identity then give weighted
second derivatives, proving (8) in the operator-domain norm.
Thus all physical hypotheses and constants are checked directly.

The audit records that the targeted Agmon/Froese–Herbst full primary
texts could not be accessed. No unread version of their decay theorem
is imported; (8) is instead proved here from the already established
form/domain facts.

**OPEN — admissible exterior approximation and matching.** The true
tail bound permits an analysis radius proportional to \(n^\alpha\).
It does not show that the polynomial-exponential approximant selected
inside that radius has a small exterior tail. An unaccounted cutoff
would change the dictionary. A needed construction must control, for
the same candidate, both its interior error and its entire physical
\(H^2_*\) error on the complement. We have not constructed that witness.
The global damped-log estimate of Section 1 does not supply the missing
ground-state remainder estimate or its global matching.

## 5. Global RATE, normalization, and effective composition

**OPEN — the requested RATE.** The result in (2) is not an approximation
of \(\psi_Z\) on all of \(\mathbb R^6\). Its normalization would not
make it one. Therefore no normalized ground-residual sequence is
asserted, and Phases 5–6 cannot be concluded.

Normalization itself would be an elementary step once the missing global
witness exists: if \(\|v_n-\psi_Z\|_2\le\varepsilon_n<1\), then
\(\|v_n\|\ge1-\varepsilon_n\), and
\[
\left\|(H_Z-E_Z)\frac{v_n}{\|v_n\|}\right\|_2
\le\frac{\|(H_Z-E_Z)(v_n-\psi_Z)\|_2}{1-\varepsilon_n}.
\tag{9}
\]
This conditional scalar identity does not supply \(v_n\). In particular,
energy error, variance, and Temple width were not used as substitutes
for a proven global graph error.

**PROVEN — previously established finite arithmetic facts remain intact.**
The exact dictionary has deterministic generation, \(m_n=O(n^4)\),
polynomial exponent and rational moment heights, the existing moment
field, and a positive rational Gram matrix after the recorded column
scaling. The supplied bound
\[
\|c\|_2^2\le2^{h_n},\qquad
h_n=m_n^2B_n+(m_n-1)\lceil\log_2(2m_n)\rceil,
\quad B_n=\operatorname{poly}(n)
\]
continues to hold for normalized dictionary vectors under those scaling
conventions. It is not re-proved here. The constructed leading-component
witnesses have the stated admissible degree and coefficient descriptions,
but they are not the missing normalized ground-state RATE witnesses.
The real fixed amplitude in (1) need not be computed for the local
existence theorem.

**OPEN — Phase 6 composition.** Because RATE is open, no actual
RATE-witness precision/regularization/rounding schedule is claimed to
give Theorem T. The final EFFECTIVE-DICTIONARY status below refers to
that requested completed phase, including its algorithm and operation
count; it does not retract the proven finite arithmetic facts.
Exponential coefficient magnitude with polynomial bit length is not
an obstruction and was not treated as one.

## 6. Adversarial findings and proof boundary

The independent [audit](dyadic_proof/ADVERSARIAL_AUDIT.md) checked the
component constructions and their increasing angular orders, physical
derivatives, scale tails, coefficients, exact index consumption, cusp
multiplier, graph-radius bookkeeping, and exterior constants.

- Dropping \(\log(\rho/S)\) would lose actual angular structure. Equation
  (3), the full Cartesian series estimate, and (4) address it.
- Retaining \(S^{-2k}\) as a basis function would change the dictionary.
  Polynomial Laplace moments remove every such inverse power.
- Allowing arbitrary exponential panel midpoints would change the nodes.
  Every Taylor center is exactly \(Z2^j\).
- Estimates at fixed angular order would not suffice. The explicit
  \(K=m,P=16m,J=4m\) allocation controls the growth and tails together.
- Treating \(e^{u/2}\) as a smooth bounded global multiplier would be
  incorrect. Its local polynomial approximation and Hardy bound account
  for both the \(1/u\) Hessian and the extra degree.
- The nonconstant \(C^{1,1}\) factor is not silently analytic. The exact
  extracted remainder and missing inequality are (1) and (7).
- Fixed isolated-pair charts do not give uniform shrinking-scale charts.
  Equation (6) identifies precisely where pair–triple overlap remains.
- True bound-state decay does not bound extrapolation of a local trial.
  Equation (8) and the missing admissible global construction are separate.
- Theorem C concerns a fixed finite exponent set. Applying its inverse
  estimate with constants independent of this expanding set would be
  invalid. No lower bound refuting the present RATE has been proved.
- Normalizing a leading-log approximation cannot create a ground-state
  approximation. The needed hypotheses of (9) remain unsupplied.

No numerical rate fits or archived E2–E10 values enter these proofs.
No new Lean result is claimed. The four subagent contributions have been
collected, checked, and integrated. The earlier decision report and
Theorem C are preserved.

DYADIC LEADING-SINGULARITY STATUS: PROVEN

PAIR-COLLISION STATUS: OPEN

REGULAR-REMAINDER STATUS: OPEN

EXTERIOR-TAIL STATUS: OPEN

GLOBAL GRAPH RATE STATUS: OPEN

EFFECTIVE-DICTIONARY STATUS: OPEN

THEOREM T STATUS: OPEN

**One next mathematical target:** prove or refute (7), the uniform
weighted factorial derivative bound for the actual extracted physical
remainder on the closed half-perimetric octant approaching its vertex.
