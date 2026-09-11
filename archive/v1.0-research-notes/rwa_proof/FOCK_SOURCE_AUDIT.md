> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Fock-source and higher-logarithm audit for RWA

Audit date: 2026-09-09. This is a bounded primary-source audit and paper calculation. No new numerical RATE experiment or Lean verification is represented here. The already-proved leading-singularity approximation theorem is not reproved.

The outcome of this source route alone is **OPEN**: no verified Fock theorem below supplies physical RWA, and the inspected higher logarithms do not refute it. The general finite-log compatibility lemma below is **PROVEN (paper)**. The separate, subsequently completed [RWA_THEOREM.md](RWA_THEOREM.md) proves physical RWA directly from the rescaled equation; it does not require a full physical Fock expansion.

## 1. Exact source applicability records

### Morgan 1986: convergence does not identify the bound-state solution

Source: J. D. Morgan III, *Convergence properties of Fock's expansion for S-state eigenfunctions of the helium atom*, Theoretica Chimica Acta 69, 181–223, [DOI 10.1007/BF00526420](https://link.springer.com/article/10.1007/BF00526420).

The primary publisher abstract was read. Full text was inaccessible; consequently no theorem number or unprinted hypothesis is attributed to it. The abstract describes pointwise convergence at all hyperradii for suitable Fock-series solutions of the six-dimensional helium equation, for even complex energy, without an infinity boundary condition. It explicitly separates the unresolved question whether the exponentially decaying physical eigenfunction admits such a representation. The reported predecessor result concerns convergence in mean on a radial interval.

There is no verified derivative norm, closed-perimetric-octant analytic radius, uniform triple-point factorial constant, or physical-series identification available from this inspected text. Thus it discharges none of RWA's missing all-order physical estimate. A later paper citing Morgan as generic “convergence of the Fock expansion” cannot erase this restriction.

### Fock 1954/1958: original source not recovered

Bibliography verified in the primary Morgan and Demkov–Ermolaev papers: V. A. Fock, Izvestiya Akademii Nauk SSSR, Ser. Fiz. 18, 161–172 (1954); English translation, *On the Schrödinger equation of the helium atom*, K. Norske Vidensk. Selsk. Forh. 31, 138–152 (1958). No verified DOI or accessible original full text was obtained in this bounded audit. Exact theorem number, function space, convergence hypotheses, boundary control, and all-order constants are therefore **unresolved**, rather than supplied from a secondary characterization.

### Demkov–Ermolaev 1959: the recurrence is accessible

Source: Yu. N. Demkov and A. M. Ermolaev, *Fock expansion for the wave functions of a system of charged particles*, Soviet Physics JETP 9, 633–635 (1959), [primary full text](https://jetp.ras.ru/cgi-bin/dn/e_009_03_0633.pdf). No DOI was verified.

There is no numbered theorem. Equations (2)–(6) derive the hyperspherical recurrence for a 3N-dimensional Laplacian and degree-minus-one Coulomb potential, starting from a series ansatz; parity restricts logarithm powers. The three-page text discusses angular finiteness/continuity and free harmonic coefficients fixed by conditions at infinity. It gives no all-order Banach norm bound or proof identifying every physical eigenfunction with a convergent series, and no uniform analytic chart estimates at pair strata. Equation (8) generalizes the recurrence to potentials with homogeneous expansions. These algebraic recurrences are useful for inspecting possible terms, not for importing RWA.

### Liverts–Krivec 2022: explicit higher coefficients, not RWA

Source: E. Z. Liverts and R. Krivec, *Fock expansion for two-electron atoms. High order angular coefficients*, [arXiv:2209.09053v2](https://arxiv.org/pdf/2209.09053), Atoms 10, 135 (2022), [DOI 10.3390/atoms10040135](https://doi.org/10.3390/atoms10040135).

No numbered regularity theorem occurs. Equations (1), (3)–(7) state the S-state expansion and angular recurrence on the six-dimensional sphere. Equations (9)–(13) give low-order angular coefficients; Sections II onward calculate selected maximal-logarithm coefficients through radial order ten. Finite angular solutions are selected, including cancellation of apparent pair-endpoint divergences. No uniform analytic neighborhood for every angular coefficient, summable analytic majorant over radial orders, or physical-series identification is proved there. Its generic convergence sentence cites Morgan and cannot supply those missing facts. The calculations below use only its displayed low-order identities and are explicitly conditional formal-series algebra.

The related [arXiv:1505.02351](https://arxiv.org/abs/1505.02351), DOI [10.1103/PhysRevA.92.042512](https://doi.org/10.1103/PhysRevA.92.042512), and [arXiv:1601.06964](https://arxiv.org/abs/1601.06964) were located as coefficient-calculation sources. Their abstract-level contents were inspected; no uninspected theorem from them is used.

## 2. A finite radial logarithm is compatible with the exact weak weight

**PROVEN (paper), finite-log compatibility lemma.** Write

\[
S(x)=x_1+x_2+2x_3,\qquad
K=\{x\in[0,\infty)^3:S(x)=1\}.
\]

Let \(F\) be holomorphic and bounded by \(M\) on the complex max-norm \(\eta\)-neighborhood of \(K\). Fix an integer \(m\ge1\), an integer \(p\ge0\), and a real \(0<\sigma<m\). Define, for \(0<S\le1\),

\[
f(x)=S(x)^m(\log S(x))^p F(x/S(x)).
\]

Set

\[
\theta=\min\{1/16,\eta/8\},\quad A=\theta^{-1},\quad
L_{p,\lambda}=\begin{cases}1&p=0,\\
2^p[1+(p/\lambda)^p]&p\ge1,
\end{cases}\quad \lambda=m-\sigma.
\]

Then every multi-index \(\nu\) satisfies

\[
|\partial^\nu f(x)|\le
M(5/4)^mL_{p,m-\sigma}\,A^{|\nu|}|\nu|!
S(x)^{\sigma-|\nu|}.
\tag{F1}
\]

This includes the nonvertex boundary by the stipulated analytic extension.

**Proof.** At a real point \(x\), put \(s=S(x)>0\). In the complex polydisc \(|z_i-x_i|<\theta s\),

\[
|S(z)-s|\le4\theta s\le s/4,\qquad
|S(z)|\in[3s/4,5s/4].
\]

Since \(0\le x_i\le s\),

\[
\left|\frac{z_i}{S(z)}-\frac{x_i}{s}\right|
\le \frac{\theta s}{3s/4}
+\frac{x_i(4\theta s)}{s(3s/4)}
\le\frac{20}{3}\theta<\eta.
\]

The branch of \(\log S(z)\) extending the real logarithm is holomorphic there and satisfies

\[
|\log S(z)|\le |\log s|+\log(4/3)<|\log s|+1.
\]

Cauchy's formula in the polydisc gives

\[
|\partial^\nu f(x)|\le
\nu!\theta^{-|\nu|}M(5/4)^m
s^{m-|\nu|}(1+|\log s|)^p.
\]

For \(p\ge1\), put \(t=-\log s\ge0\). Using \((1+t)^p\le2^p(1+t^p)\) and
\(\sup_{t\ge0}e^{-\lambda t}t^p=(p/(e\lambda))^p\),

\[
s^{m-\sigma}(1+|\log s|)^p\le L_{p,m-\sigma}.
\]

For \(p=0\) this factor is at most one. Finally \(\nu!\le|\nu|!\). This proves (F1). No radial derivative order is hidden in \(A\) or the leading constant. \(\square\)

**Consequences and limits.** Every finite sum with \(m>\sigma\) and uniformly analytic angular factors satisfies the same type of estimate, using the maximum of finitely many \(A\)'s and the sum of constants. Higher logarithm powers do not inherently change factorial analyticity to Gevrey regularity. An infinite sum needs a common angular neighborhood and a summable analytic majorant; neither follows from termwise finiteness or scalar pointwise convergence. A factor singular at an angular edge does not satisfy this lemma's hypothesis. Thus the angular hypothesis cannot be dropped when testing the closed octant.

## 3. The next formal logarithms survive the prescribed extraction

The following is **PROVEN conditional algebra**: if a solution has the displayed Fock coefficients, its conjugated expansion has the terms computed here. It is not a new theorem asserting that the physical ground state has a full Fock expansion.

Use \(\rho=\sqrt{r^2+s^2}\), \(\xi=u/\rho\), \(\eta=S/\rho\), \(\kappa=Z(2-\pi)/(3\pi)\). Denote the homogeneous order-one cusp term by

\[
F_1=-ZS+u/2.
\]

The coefficient identities cited above give

\[
\psi_{21}=\kappa(1-\xi^2),\qquad
\psi_{31}=-\frac{\kappa}{12}
\{6Z\eta(1-\xi^2)+\xi(5\xi^2-6)\}.
\]

Multiplying the formal wavefunction by \(e^{-F_1}\), the cubic coefficient of \(\log\rho\) is therefore

\[
\begin{aligned}
\rho^3\psi_{31}-F_1\rho^2\psi_{21}
&=\kappa\rho^3\left[
\frac{Z\eta}{2}(1-\xi^2)+\frac{\xi^3}{12}\right]\\
&=\kappa\left(ZS q+\frac{u^3}{12}\right).
\end{aligned}
\tag{F2}
\]

In the last equality \(\rho^2-u^2=2q\) was used. This cubic logarithm is generally nonzero after subtracting the quadratic leading logarithm. On \(r=s>0,u=0\), its polynomial coefficient equals \(2\kappa Zr^3\ne0\).

The next maximal-logarithm coefficient is a quartic harmonic polynomial. Direct substitution into the displayed hyperspherical harmonics yields

\[
\rho^4\psi_{42}
=\frac{Z^2(\pi-2)(5\pi-14)}{180\pi^2}
\{\rho^4-8r^2s^2+8q^2\}.
\tag{F3}
\]

It multiplies \((\log\rho)^2\); cusp conjugation cannot remove its lowest-order double logarithm, because the conjugating exponential contains no logarithm.

Both (F2) and (F3) are compatible with (F1), since their coefficients are ordinary distance polynomials and

\[
\log\rho=\log S+\log(\rho/S),\qquad
\rho^2/S^2\in[1/2,1]
\]

on the closed normalized octant. The angular factor \(\log(\rho/S)\) extends holomorphically to a fixed neighborhood of this compact simplex: its squared argument is a polynomial there, bounded away from zero on the real simplex, so one common complex neighborhood and logarithm branch exists. Thus neither a cubic single logarithm nor a quartic double logarithm refutes RWA for any fixed \(0<\sigma<1\).

## 4. A precise nonphysical countermodel to an invalid inference

**PROVEN (paper).** The facts “Cartesian \(C^{1,1}\)” and “reduced analytic extension at every nonvertex point” do not, by themselves, imply RWA.

Define

\[
f(x_1,x_2)=\begin{cases}
\rho^6\sin(1/\rho),&\rho>0,\\0,&\rho=0.
\end{cases}
\]

It is rotation and exchange invariant. Ordinary radial differentiation shows \(|Df|=O(\rho^4)\) and \(|D^2f|=O(\rho^2)\), so it extends as a Cartesian \(C^2\) function. In half-perimetric variables \(\rho=\sqrt{(b+c)^2+(a+c)^2}\) is real analytic in a neighborhood of every nonvertex closed-octant point; hence so is the reduced \(f\).

On the edge \(a=b=0,c=t>0\),

\[
f=8t^6\sin(1/(\sqrt2t)).
\]

The sixth \(c\)-derivative has a nonzero leading oscillatory term of order \(t^{-6}\), with all other terms \(O(t^{-5})\). Along a sequence where that leading sine factor has magnitude one, it cannot be bounded by any fixed multiple of \(t^{\sigma-6}\) with \(\sigma>0\). The example does **not** solve the Coulomb equation and is **not** a physical refutation. It isolates why a quantitative PDE theorem, rather than just qualitative regularity, remains necessary.

## 5. Narrow conclusion

No inspected primary theorem turns the known physical leading-log extraction into an all-order estimate for the physical remainder. The actual obstruction to this source-based route is physical identification together with uniform analytic angular control, not the mere existence of higher radial logarithms. This file does not claim that RWA itself is false. A direct proof from the rescaled physical PDE could avoid the need for any full Fock-series representation.
