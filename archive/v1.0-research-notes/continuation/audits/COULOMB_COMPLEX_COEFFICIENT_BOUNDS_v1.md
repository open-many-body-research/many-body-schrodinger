> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit common complex neighborhoods for the Coulomb coefficients

Evidence category: **paper proof**. This verifies the coefficient and source
inputs for the new KS and nonsingular operator lemmas. It supplies no
physical eigenfunction, spectrum or formal verification.

Fix \(Z\ge0\), \(E\in\mathbb R\), and a finite scale bound
\(\varepsilon_0>0\). The scale throughout is \(0<\varepsilon\le\varepsilon_0\).
For a complex vector, its Hermitian Euclidean norm is used only in estimates;
it is never substituted for a holomorphic squared-distance polynomial.

## 1. The reciprocal-distance branch

Let \(x\in\mathbb R^3\) with \(|x|\ge d>0\), and let
\(\zeta\in\mathbb C^3\), \(\|\zeta\|_2\le d/8\). Set
\[
 q_x(\zeta)=\sum_{j=1}^3(x_j+\zeta_j)^2.
\]
This is a holomorphic polynomial, and
\[
 |q_x(\zeta)-|x|^2|
 \le2|x|\|\zeta\|_2+\|\zeta\|_2^2
 \le {17\over64}|x|^2.                                          \tag{C1}
\]
Thus the image lies in a disc in the right half-plane centered at the
positive real value \(|x|^2\). The binomial series
\[
 R_x(\zeta)=|x|^{-1}
       \left(1+{q_x(\zeta)-|x|^2\over|x|^2}\right)^{-1/2}
\]
defines a single holomorphic branch on the whole displacement ball,
positive at zero. Its square is \(q_x^{-1}\), so
\[
 |R_x(\zeta)|\le {8\over\sqrt{47}|x|}\le{2\over d}.               \tag{C2}
\]
For real \(\zeta\) it agrees with the physical reciprocal distance.
No continuation around a zero or branch cut is involved.

## 2. Nonsingular Cartesian charts

Let \(X^0=(X_1^0,X_2^0)\in\mathbb R^6\) satisfy
\[
 |X_1^0|,\ |X_2^0|,\ |X_1^0-X_2^0|\ge d>0,
\qquad R={d\over16\sqrt3}.
\]
On the complex sup polydisc \(|X-X^0|_\infty<R\), each nuclear displacement
has Euclidean norm at most \(\sqrt3R\), and the pair displacement has
norm at most \(2\sqrt3R=d/8\). Apply Section 1 to the three real
separation centers. The analytic extension of
\[
 V(X)=-Z/|X_1|-Z/|X_2|+1/|X_1-X_2|
\]
has bound
\[
 |V(X)|\le {2(2Z+1)\over d}.                                    \tag{C3}
\]
The notation for the complex function means the branches just constructed,
not a Hermitian absolute value.

For the actual scaled potential
\[
 B_\varepsilon=2\varepsilon V-2\varepsilon^2 E,
\]
put
\[
 M_{\rm cart}={4(2Z+1)\over d}+2\varepsilon_0|E|.
\]
Then \(|B_\varepsilon/\varepsilon|\le M_{\rm cart}\) on the full
complex polydisc. At every real point of its half polydisc, Cauchy's
estimate gives
\[
 |D^\eta(B_\varepsilon/\varepsilon)|
 \le M_{\rm cart}(2/R)^{|\eta|}\eta!
 \le M_{\rm cart}(2/R)^{|\eta|}|\eta|!.                           \tag{C4}
\]
One can apply the nonsingular elliptic lemma with outer half-width \(R/2\),
base half-width \(a=R/4\), initialization gap \(e_0=R/16\), and
\(\rho=\min(a/2,1)\). For centers on the normalized two-electron shell,
\(d\le1\), so \(\rho=R/8\) is permitted. Use analytic growth constant
\(\max(1,2/R)\) and potential prefactor
\(\max(1,\varepsilon_0M_{\rm cart})\).

## 3. Fixed normalized nuclear KS chart

Use the explicit KS polynomial \(K\) from KS_WEAK_REMOVABILITY_v1.md,
and write
\[
 \varrho(y)=\sum_{j=1}^4y_j^2,\qquad h=1/32.
\]
Consider the **complex** polydisc
\[
 |y|_\infty<h,\qquad |t-e_3|_\infty<h.
\]
On this domain
\[
 |\varrho(y)|\le\|y\|_2^2\le4h^2=1/256.
\]
For complex \(y\), do not use the real identity \(|K(y)|=|y|^2\).
Instead each of the three KS components has absolute value at most
\(\|y\|_2^2\), directly from \(2|ab|\le|a|^2+|b|^2\). Therefore
\[
 \|K(y)\|_2\le\sqrt3\,\|y\|_2^2\le\sqrt3/256.                    \tag{C5}
\]
The displacements of \(t\) about \(e_3\), and \(K(y)-t\) about \(-e_3\),
are respectively at most
\[
 \sqrt3/32,\qquad 9\sqrt3/256<1/8.
\]
Section 1 therefore gives one positive-real branch for both inverse
distances on this entire complex polydisc, each bounded by 2.

The normalized nuclear coefficient is exactly
\[
 b_\varepsilon:=B_\varepsilon/\varepsilon
 =-8Z+8\varrho(y)\left(-Z R(t)+R(K(y)-t)\right)
                      -8\varepsilon E\varrho(y),
\]
where each \(R\) denotes the just-defined branch at its corresponding
real center. It obeys
\[
 |b_\varepsilon|\le
 M_{\rm nuc}:=8Z+{Z+1\over16}+{\varepsilon_0|E|\over32}.           \tag{C6}
\]
The normalization is the physical operator
\(-\Delta_y-4\varrho(y)\Delta_t+B_\varepsilon\).

## 4. Fixed normalized electron-pair KS chart

Use the identical complex polydisc centered at \((y,t)=(0,e_3)\).
The two nuclear vectors \(t\pm K(y)/2\) are perturbations of \(e_3\)
of Euclidean norm at most
\[
 \sqrt3/32+\sqrt3/512=17\sqrt3/512<1/8.
\]
Their reciprocal-distance branches therefore both exist and are bounded
by 2. The exact pair coefficient is
\[
 b_\varepsilon
 =4-4Z\varrho(y)\left(R(t+K(y)/2)+R(t-K(y)/2)\right)
                       -4\varepsilon E\varrho(y),
\]
and
\[
 |b_\varepsilon|\le
 M_{\rm pair}:=4+{Z\over16}+{\varepsilon_0|E|\over64}.              \tag{C7}
\]
The corresponding physical operator is
\(-\Delta_y-\varrho(y)\Delta_t+B_\varepsilon\).
The pair collision at normalized distances \(r=s=1,u=0\) has precisely
\(t=e_3,X=0\) in relative and center coordinates.

For either chart, every real point in the half polydisc has complex
coordinate margin \(h/2\). Hence, with \(M_b=M_{\rm nuc}\) or
\(M_{\rm pair}\),
\[
 |D^\eta b_\varepsilon|
      \le M_b\,64^{|\eta|}\eta!
      \le M_b\,64^{|\eta|}|\eta|!.                               \tag{C8}
\]
These estimates are uniform for the whole declared scale interval and
all derivative orders. If a lemma requires its constants to be at least
one, replace a prefactor by its maximum with one. The real weak equations
use \(\varrho(y)=|y|^2\); the complex continuation uses its polynomial
meaning throughout.

## 5. Source amplitudes and physical chart containment

For \(a_0=\psi(0)\), the normalized differences in both operator lemmas
have source \(f_\varepsilon=-a_0b_\varepsilon\). Equations (C4) and
(C8) therefore give the required pointwise analytic source bounds with
prefactor \(|a_0|M_b\). The corresponding L2 prefactor on any fixed
outer box is at most
\[
 |a_0|M_b\,|\text{outer box}|^{1/2}.                              \tag{C9}
\]
No unknown derivative of \(\psi\) enters this source estimate.

For completeness, the local Lipschitz hypothesis can be used on one common
physical ball. Suppose it holds on a ball of radius \(R_{\rm phys}>0\)
about the simultaneous collision, and take
\[
 0<\varepsilon_0\le R_{\rm phys}/2.
\]
On the real half KS boxes, \(|y|\le h\) and
\(|t|\le1+\sqrt3h/2\). The physical displacement divided by
\(\varepsilon\) is
\[
 \sqrt{|y|^4+|t|^2}\quad\hbox{for the nuclear chart},\qquad
 \sqrt{2|t|^2+|y|^4/2}\quad\hbox{for the pair chart},
\]
both strictly less than 2.

At a normalized nonsingular center,
\(|X_1^0|,|X_2^0|\le1\), so \(\|X^0\|_2\le\sqrt2\). For
\(d\le1\), every real point in the Cartesian outer half box satisfies
\[
 \|X\|_2\le\sqrt2+\sqrt6R/2\le33\sqrt2/32<2.
\]
Thus every relevant real scaled image lies in the one physical Lipschitz
ball. This supplies the actual uniform amplitude hypotheses of the
operator lemmas on the same scale interval as their coefficient bounds.

## 6. Exact scope and frozen provenance

The two normalized nuclear vertices are related by electron exchange.
The pair vertex is covered by Section 4. Away from these three vertices,
any compact normalized set has a positive lower bound on the three
distances, and Section 2 applies with that bound \(d\). The coefficient
proof does not assume that a nonsingular Cartesian chart remains uniform
when its separation \(d\) tends to zero; the pair charts handle that
frontier.

Combined with the weak KS, H12, factorial, direct coefficient descent,
nonsingular elliptic and boundary-germ lemmas, these estimates eliminate
the analytic coefficient-neighborhood placeholders from the local
paper-level chain. Actual physical existence, Lipschitz regularity,
rotational invariance, spectral identification and formalization remain
explicit independent obligations.

Frozen target: rwa_proof/UNIFORM_ANALYTIC_AUDIT.md sections 1–2,
SHA-256 5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c,
relative to THEOREM_T_FREEZE_2026-09-09_212604/.
Frozen commit: 166f43f2f0178f92d8c4d1dde209ef0eeaefa660;
tag theorem-t-proof-freeze-2026-09-09.

The exact lifted operators are proved in the new
KS_WEAK_REMOVABILITY_v1.md, SHA-256
ba8769955d76e01ce561a68071ad5832828106c3ca614ea8fe1e19c36aa78cde.
The nonsingular operator theorem is NONSINGULAR_ELLIPTIC_FACTORIAL_v1.md,
SHA-256 d776fd6de1ea4df30b5bbddfa0197d3d68c32b84514b9c5ccaaaebfb0d07feb0.

Every estimate above is proved directly by polynomial inequalities,
a convergent binomial branch and Cauchy's formula. No inaccessible
reference or empirical bound is used. No frozen or sealed artifact was
changed. The auxiliary coulomb_complex_checks_v1.py records exact
rational checks of the displayed numerical constants; review and sealing
are recorded separately.
