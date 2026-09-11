> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

> ⚠️ **Unfinished report.** The only completed H₂ certificate has width 0.75 Ha and its lower endpoint is the a-priori bound. See [ERRATUM-002](../../../errata/ERRATUM-002-h2-enclosure-trivial.md).

# H₂ at R = 7/5: continuum certificate and molecular separator

All energies in this report are in hartree, for two unit point nuclei at
\((0,0,\pm7/10)\), two electrons, and infinite nuclear masses. Nuclear repulsion
is **excluded**. The earlier survey was not rerun. The later compute-offload request separately authorized higher-order helium verification; those results are recorded in COMPUTE_OFFLOAD.md.

## Result and status

The separator is proved: \(\beta=-91/50\) in a reducing symmetry sector containing
the physical fermionic ground state. There is no missing separator lemma for
this fixed instance. The full continuum proof, including the identification of
the physical ground, is [separator.md](h2/separator.md).

**PROVEN (paper proof and rational arithmetic, outside Lean).** The numerical
enclosure and its exact endpoints are recorded below after the completed computation. The refined result intersects separately certified pair enclosures and records that reuse explicitly. Neither the candidate optimizer nor the published reference is an input
to the proof. The final width is the computed width, rather than a requested
quadrature tolerance.

<!-- FINAL_CERTIFICATE -->

**PROVEN (Lean).** Seven new scalar theorems were compiled, with no added axioms,
`sorry`, or `native_decide`. They check the parity threshold arithmetic, an
alternative resolvent bound's scalar algebra, and lower bounds on the width
of a fixed trial/separator Temple interval. The continuum operator, Gaussian
integration code, and rational arithmetic execution are **not** formalized in
Lean. This distinction is essential to the scope of the result.

**EMPIRICAL.** Floating-point optimization selected the rational trial. It is
not trusted by the certificate. The published comparison value below is also
empirical and is used only after certification.

**CONJECTURED.** No general tractability or complexity theorem is asserted.
The present computation does not establish a polynomial cost bound in the
number of requested digits.

## 1. A separator that works for this molecule

The one-electron operator is

\[
h=-\tfrac12\Delta-|x-A|^{-1}-|x-B|^{-1},\qquad D(h)=H^2(\mathbb R^3).
\]

Let \(g,u\) denote its inversion-even and inversion-odd sectors. For the
charge-two hydrogenic operators \(k_C=-\Delta/2-2/|x-C|\), the exact atomic
spectrum gives

\[
k_C\ge-\tfrac12I-\tfrac32P_C,
\qquad h=(k_A+k_B)/2\ge-\tfrac12I-\tfrac34(P_A+P_B),
\]

where \(P_C\) projects onto \(e^{-2|x-C|}\). The operator \(P_A+P_B\) has
**one direction in each parity sector**. Therefore each parity restriction
has at most one eigenvalue below \(-1/2\). A two-dimensional spectral subspace
below that cutoff would contain a nonzero vector orthogonal to the relevant
rank-one direction, contradicting the form inequality. This establishes the
spectral index needed for Temple; a numerical approximation to an excited
level is not used as a separator.

The rational Slater trials

\[
e^{-(6/5)|x-A|}+e^{-(6/5)|x-B|},\qquad
e^{-(3/5)|x-A|}-e^{-(3/5)|x-B|}
\]

have means below \(-1/2\). Their independently executed strong-moment
certificate gives the exact lower bounds

\[
e_g\ge-3929/2996>-33/25,\qquad
e_u\ge-1591/2100>-4/5.
\]

The [one-electron JSON](h2/slater_moments.json),
[source](h2/slater_moments.py), and [log](h2/slater_moments.log) include the
means, variances, special-function series and explicit remainder bounds.
Their inputs were recomputed for these nuclei and this separation; no
external H₂⁺ numerical result is assumed.

For two electrons use the spatial sector \(\mathcal K\) that is symmetric
under exchange and even under simultaneous inversion. It decomposes as
\(\operatorname{Sym}^2\mathfrak h_g\oplus\operatorname{Sym}^2\mathfrak h_u\).
If \(P\) projects onto the product of the even one-electron ground state
with itself, then \(\operatorname{rank}P=1\), and positive repulsion yields

\[
H_{\mathcal K}\ge-\frac{66}{25}P-\frac{91}{50}(I-P).
\tag{1}
\]

Indeed, outside \(P\), the even-even sector has at least one electron above
\(-1/2\), giving \(-33/25-1/2=-91/50\). The odd-odd sector is bounded below
by \(-8/5>-91/50\). Thus a trial mean below \(-91/50\) proves that the
spectral subspace below this cutoff is exactly one-dimensional.

This symmetry restriction is justified for the original physical ground:
\(h\ge-33/25\), and HVZ gives the scalar two-electron essential-spectrum
threshold \(\inf\sigma(h)\). The certified molecular trial lies below that
threshold. The scalar ground therefore exists and is simple and strictly
positive by the positivity-improving Coulomb semigroup. Exchange and
simultaneous inversion fix it, so it belongs to \(\mathcal K\). Multiplying
it by the spin singlet gives a physical fermionic ground state, with the
same energy. The ionization threshold is at least -33/25 while the trial mean is below -91/50, so the ionization margin is greater than 1/2 hartree. Every fermionic spin component is bounded below by the scalar
ground energy. [The complete proof](h2/separator.md) states the domains,
Kato–Rellich/HVZ dependencies and the explicit short-time Coulomb bounds
needed in the positivity argument.

Consequently, for the supplied trial and for any other normalized
\(\Phi\in D(H)\cap\mathcal K\) with mean \(m<\beta=-91/50\),

\[
m-\frac{v}{\beta-m}\le E_0\le m,
\qquad v=\|H\Phi\|^2-m^2.
\tag{2}
\]

To prove (2), integrate the nonnegative spectral polynomial
\((\lambda-E_0)(\lambda-\beta)\) against the trial spectral measure. This
gives \(v\ge(m-E_0)(\beta-m)\); division by the positive denominator proves
the result. Only \(\Phi\in D(H)\) is needed, not \(\Phi\in D(H\circ H)\).
The number \(\beta\) is not asserted to bound the second eigenvalue of the
operator on **all** spin and parity sectors.

## 2. Rational trial and exact continuum moments

The chosen trial is supplied in
[trial_ecg_pruned_back64.json](h2/trial_ecg_pruned_back64.json).
It has 64 basis functions. Every exponent matrix, axial center and linear
coefficient is an exact rational string. For each rational positive-definite
\(2\times2\) matrix \(A_j\) and rational axial vector \(p_j\), define

\[
g_j(x_1,x_2)=\exp\!\left[-\sum_{d=1}^3
 (x^d-p_j^d)^TA_j(x^d-p_j^d)\right],\qquad
\phi_j=\sum_{U\in\{1,S,J,SJ\}}Ug_j,\qquad
\Phi=\sum_jc_j\phi_j.
\]

Here \(p_j^1=p_j^2=0\), \(p_j^3=p_j\); \(S\) exchanges the electrons and
\(J\) inverts both positions. Repeated images in the sum are retained. Each
primitive is Schwartz, so this finite sum belongs to spatial \(H^2\).
Multiplying by \(\uparrow\downarrow-\downarrow\uparrow\) gives an
unnormalized antisymmetric trial with rational spin coefficients. All
normalization is performed through moment quotients. No irrational
variational coefficient is an input.

The checker verifies positive definiteness, symmetry, geometry, energy
convention and rational types before computing. The choice of Gaussians
makes the differentiated trial polynomial times Gaussian; thus the full
strong second moment can be computed without differentiating a cusp or
discarding any Coulomb cross terms.

For a primitive pair set \(W=A+B\), \(V=W^{-1}\),
\(\mu=V(Ap+Bq)\), and
\(\xi=p^TAp+q^TBq-\mu^TW\mu\). Its overlap divided by \(\pi^3\) is
\(s=e^{-\xi}(\det W)^{-3/2}\). The kinetic action divided by the primitive
is the polynomial

\[
K_A(x)=3\operatorname{tr}A-2\sum_d(x^d-p^d)^TA^2(x^d-p^d).
\]

Writing the five signed Coulomb terms as \(V_C=\sum_{\alpha=1}^5q_\alpha C_\alpha\),
the three primitive moments are exactly

\[
s,\qquad s\,\mathbb E(K_A+V_C),\qquad
s\,\mathbb E[(K_A+V_C)(K_B+V_C)].
\tag{3}
\]

The expectation is under the completed-square product Gaussian. Equation
(3) computes \(\langle H\phi_i,H\phi_j\rangle\) in the original continuum;
the finite Hamiltonian matrix is never squared to approximate this quantity.
Every one of the five inverse squares and ten distinct mixed products is
included with its sign and multiplicity.

All algebraic formulas and their proofs are in [THEORY.md](h2/THEORY.md).
The [independent moment derivation](h2/moment_audit.md) reduces every axial
double-Coulomb integral to one dimension, with separate treatment of
proportional linear forms and coincident centers. For example, if Gaussian
three-vectors have variances \(aI/2,bI/2\), covariance \(cI/2\), axial means
\(m,n\), and \(r=c^2/(ab)<1\), the required expectation is

\[
\frac4{\pi\sqrt{ab}}\int_0^1
\frac{e^{-(n^2/b)z^2}}{\sqrt{1-rz^2}}
F_0\!\left(\frac{(m-cn z^2/b)^2}{a(1-rz^2)}\right)dz,
\quad F_0(t)=\int_0^1e^{-tu^2}\,du.
\tag{4}
\]

The [quadrature proof](h2/quadrature.md) supplies rationally bounded
Gauss–Legendre nodes, weights, a Cauchy bound on the sixteenth derivative,
and the explicit error

\[
\frac{\ell^{17}(8!)^4}{17(16!)^3}\sup|f^{(16)}|
\]

on each cell of length \(\ell\). Proportional forms use an independently
derived prolate formula with an explicit Taylor remainder. Exponentials,
Boys functions, erfc, arctangents and \(\pi\) use explicit series or tail
bounds. Every arithmetic operation has outward rational endpoints. A
quadrature resource cap leaves the full proved remainder in the result.
Small contributions may use the proved bound
\(0\le\mathbb E(C_\alpha C_\beta)\le2/\sqrt{a_\alpha a_\beta}\).

## 3. Verification and comparison

The fresh checker recomputes the signed contraction with outward 128-bit
dyadic intervals. Exact fractions select every sign and perform all
normalization and endpoint rounding. The common symmetry/overlap factor
\(4\pi^3\) cancels from every quotient. Source and input SHA-256 hashes are
recorded with the result.

The independent [audit source](h2/independent_audit.py) and
[audit log](h2/independent_audit.log) check the kinetic formulas by direct
Cartesian differentiation and a separate Gaussian integration-by-parts
recurrence. They also check Coulomb formulas using independent exact
series, special cases, and the original two-dimensional representation.
Finite exact tests supplement the general paper derivations; they are not
presented as a universal formal proof of Python code.

The most precise published exact-R benchmark verified here is Pachucki, **arXiv:1007.0322v2**,
DOI [10.1103/PhysRevA.82.032509](https://doi.org/10.1103/PhysRevA.82.032509),
Table IV, row \(R=1.40\). Its total BO energy is
\(-1.1744757142204434(5)\). Subtracting the nuclear repulsion **exactly** gives

\[
E_{\rm ref}=-1.1744757142204434-\frac57
\simeq-1.8887614285061576857.
\]

The separate equilibrium value at \(R=1.4011\) is not used. The reference's
extrapolation and parenthetical uncertainty are empirical; neither
contributes to the certified lower bound.

<!-- FINAL_AUDIT_AND_DISCREPANCY -->

## 4. Lean scope and reproduction

[TempleScalars.lean](formal/TempleScalars.lean) adds seven public theorems:

1. `parity_two_electron_separator`: the explicit even-even or odd-odd
   scalar energy hypotheses imply the minimum of the two summed thresholds.
2. `h2_parity_separator_value`: that minimum is exactly \(-91/50\) for the
   supplied rational thresholds.
3. `h2_parity_separator_rational`: the specialized hypotheses imply the
   rational separator inequality.
4. `stieltjes_polynomial_identity`: the scalar resolvent slack equals the
   stated polynomial divided by a proved positive denominator.
5. `stieltjes_rank_one_scalar`: nonnegativity of that polynomial implies
   the scalar resolvent inequality.
6. `temple_width_lower_bound`: lower bounds on the mean and variance
   give a lower bound on the exact width for this fixed trial and separator.
7. `temple_width_target_obstruction`: if that lower bound exceeds the target,
   the exact Temple width exceeds the target.

The two Stieltjes theorems belong to a documented alternative one-electron comparison;
they are not needed in the numerical parity certificate. Each theorem has
a complete human-readable proof and its own explanatory paragraph in
[H2_SCALAR_STATEMENTS.md](formal/H2_SCALAR_STATEMENTS.md). Their hypotheses
do not silently assert a continuum operator fact. The previous
finite-dimensional Hermitian Temple theorem in [Temple.lean](formal/Temple.lean)
is preserved.

Versions: **Lean 4.34.0-rc2**, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`, and **Mathlib** commit
`d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`.
The [scoped build log](formal/h2-standalone/logs/lake-build.log) reports success
(8914 jobs), exit code zero. The [axiom audit](formal/h2-standalone/logs/axiom-audit.log)
covers **83 public theorems** in the four scoped modules, including the seven
new ones. Only `propext`, `Classical.choice`, and `Quot.sound` occur.
The source audit finds no `sorry`, `admit`, added `axiom`, or `native_decide`.
The standalone bundle contains only the four scientific modules and a pinned
minimal configuration, so concurrent Hubbard development cannot change its
reproduction. See [verification instructions](formal/h2-standalone/README.md).

From this workspace, the numerical reproduction command is:

```sh
python3 h2/check_trial.py h2/trial_ecg_pruned_back128.json \
  --bits 128 --weighted-budget 1/100000 --workers 8 --fresh
python3 h2/independent_audit.py
```

The first command deliberately bypasses pair caches. It may take substantial
time. No helium command is part of this reproduction. The Lean verification
commands and exact pinned configuration are in the linked log directory.

## 5. What this adds, and what remains

This is a molecular ground-state certificate: it retains both nuclear
singularities at the exact geometry, treats all displaced double-Coulomb
moments in \(\|H\Phi\|^2\), and supplies a valid continuum separator even
though the atomic one-direction argument does not directly transfer. The
key additional step is splitting the one-electron two-direction comparison
by inversion, then proving that the two-electron physical ground lies in
the symmetry sector where only one low direction survives.

The separator construction does not provide a uniform molecular theorem.
For other homonuclear geometries one must recompute lower bounds
\(g(R),u(R)\) and an excited even-sector threshold \(\gamma(R)\), and prove

\[
m(R)<\min\{g(R)+\gamma(R),2u(R)\}.
\]

A positive ionization margin alone does not imply this inequality. At large
separation the even and odd one-electron levels approach one another, and
dropping electron repulsion may make the comparison too weak. A
heteronuclear molecule also loses the inversion decomposition used here.
It would need a finite-rank intermediate-operator construction or another
certified excitation bound. These are separate analytic obligations, not
consequences of adding more trial functions.

The precise remaining numerical task for this fixed H₂ route is to supply
a rational, symmetry-correct \(\Phi\in H^2\) whose certified intervals obey

\[
m_+< -91/50,\qquad
(m_+-m_-)+\frac{v_+}{-91/50-m_+}\le10^{-5}.
\]

Such a certificate would meet the requested width using the separator
already proved here. No missing spectral-index hypothesis may be replaced
by agreement with the published energy.
