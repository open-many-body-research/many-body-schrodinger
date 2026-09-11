> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Lithium continuation: continuum, symmetry, collision geometry, and verification boundary

Date: 2026-09-09. Version: v1. Electron count is **N**; approximation order is **n**. This is new post-freeze work. None of the frozen `PROVEN` labels is accepted merely because it appears in a report.

The strongest result established here is a **paper derivation with explicitly identified standard continuum inputs**, supplemented by exact rational arithmetic: the actual infinite-nuclear-mass, nonrelativistic, three-electron lithium Hamiltonian has a bound ground eigenspace; its ground states have total spin S=1/2; and its ground energy satisfies

\[
\boxed{-81/8\ \le E_{3,3}\ \le -1115626801/153055008.}
\]

The upper endpoint is the mean of one explicitly normalized continuum Slater determinant with a rational common orbital charge. This is a coarse variational enclosure, not a requested-precision energy algorithm. No lithium approximation rate, Lean continuum theorem, orbital-ground-state L=0 theorem, numerical ionization margin, or polynomial precision-cost theorem is established here. Ground existence is an application of established HVZ/Zhislin results; the spin comparison and trial are elementary deductions, not claimed as novel research.

## 1. Frozen provenance and scope

The actual readable frozen snapshot is `THEOREM_T_FREEZE_2026-09-09_212604/`. The separately named `THEOREM_T_FREEZE_2026-09-09/` remains subject to the user's immutability instruction; nothing has been written into either path. All paths below are relative to the actual snapshot. The following hashes were independently recalculated and matched `FREEZE_MANIFEST.json`:

| Frozen path | SHA-256 |
|---|---|
| `RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` |
| `TWO_ELECTRON_THEOREM.md` | `7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79` |
| `rwa_proof/RWA_THEOREM.md` | `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09` |
| `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md` | `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c` |
| `CORRECTION_PROTOCOL.md` | `1bdb5c1b27de5eaf21b635b08581131c84f4436cff342b45f67fae8f82db2bb3` |

Commit: `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`. Annotated tag: `theorem-t-proof-freeze-2026-09-09`.

These files were read for this subtask. This report is not a substitute for the separate audit of the entire `RWA_REPORT.md` dependency graph. In particular it does not independently certify the frozen two-electron analytic proof. The N=3 transfer obstruction below is a failure of a proposed extension, not a claim that the explicitly N=2 separation lemma is false.

## 2. Actual operator, including domain and all spin components

For N=3 and Z=3 define

\[
\mathcal H_-^{(3)}=\bigwedge^3 L^2(\mathbb R^3;\mathbb C^2)
\subset L^2(\mathbb R^9;(\mathbb C^2)^{\otimes3}),
\]
\[
H_{3,3}=-\frac12\sum_{i=1}^3\Delta_i
-3\sum_{i=1}^3\frac1{|x_i|}
+\sum_{1\le i<j\le3}\frac1{|x_i-x_j|},
\quad D(H_{3,3})=H^2(\mathbb R^9;\mathbb C^8)\cap\mathcal H_-^{(3)}.
\]

The form domain is H^1 intersected with the same fermionic space. Spin uses counting measure, space uses Lebesgue measure. Potentials are multiplication operators defined almost everywhere; assigning a value to the collision sets of measure zero does not remove their singularity or change the domain. The ground energy is the infimum of the spectrum of this self-adjoint restriction, equivalently the infimum of its form Rayleigh quotient.

Here is the domain argument, with its standard inputs exposed. Sliced three-dimensional Hardy gives

\[
\| |x_i|^{-1}f\|_2\le2\|\nabla_i f\|_2,
\qquad
\| |x_i-x_j|^{-1}f\|_2
\le\|(\nabla_i-\nabla_j)f\|_2.
\]

For the second estimate use the orthogonal coordinate y=(x_i-x_j)/sqrt(2), so that the factor sqrt(2) from Hardy is exactly canceled by the coordinate gradient normalization. Consequently for general finite N,

\[
\|V_{N,Z}f\|_2\le\sqrt N(2Z+N-1)\|\nabla f\|_2.
\]

Fourier interpolation \(\|\nabla f\|_2\le\epsilon\|\Delta f\|_2+(4\epsilon)^{-1}\|f\|_2\) makes V infinitesimally Laplacian-bounded. Kato–Rellich gives self-adjointness on H^2 and equivalence of H^2 with the operator graph norm. The finite permutation and spin projections preserve H^2 and commute with the operator on that domain; hence the fermionic restriction is reducing and self-adjoint. Hardy, Fourier/Plancherel and Kato–Rellich are standard analytic dependencies, not Lean results in this deliverable.

## 3. Exact spin reduction; no positive singlet scalar substitution

Let \(S_z\) be the sum of the three one-electron spin-z matrices. The four possible eigenvalues are ±3/2 and ±1/2. H commutes with these projections and with global spin flip, which identifies the positive and negative sectors.

The map which lowers the spin of an all-up vector sends its one spatial component g into the three spin components with one down spin. These components are all g. Its squared norm and energy form are both multiplied by three; after division by sqrt(3) it is an isometry intertwining H. Thus the infimum in S_z=1/2 is no greater than that in S_z=3/2. Decomposing every Rayleigh quotient into its four orthogonal S_z sectors proves

\[
\inf\sigma(H_{3,3})
=\inf\sigma(H_{3,3}|_{S_z=1/2}).
\tag{S1}
\]

This argument uses neither a ground eigenvector nor a guessed total-spin ground symmetry.

The sector in (S1) is isometric to

\[
\mathcal K=\{f\in L^2(\mathbb R^9):f(x_2,x_1,x_3)=-f(x_1,x_2,x_3)\}.
\]

For f in this space set

\[
(Tf)_{\uparrow\uparrow\downarrow}(x)=f(x_1,x_2,x_3)/\sqrt3,
\]
\[
(Tf)_{\uparrow\downarrow\uparrow}(x)=-f(x_1,x_3,x_2)/\sqrt3,
\qquad
(Tf)_{\downarrow\uparrow\uparrow}(x)=f(x_2,x_3,x_1)/\sqrt3,
\]

and set the other five components to zero. Checking the two adjacent transpositions verifies full fermionic antisymmetry. Each component is a coordinate permutation of f, so T preserves L^2, H^2, and the energy form. Conversely fermionic antisymmetry determines every component from the up-up-down component and makes that component antisymmetric in x1,x2; hence T is onto the sector. The scalar operator on \(\mathcal K\) is still the **full nine-dimensional Coulomb differential operator**. It is not a scalar positive bosonic problem, a finite-dimensional approximation, or a declaration that the ground has orbital L=0.

A completely symmetric spatial factor cannot be tensored with a nonzero totally antisymmetric three-spin tensor: \(\bigwedge^3\mathbb C^2=0\). For the same reason every continuous full fermionic wavefunction satisfies

\[
\Psi(t,t,t)=0\quad\text{as a spin tensor, for every }t\in\mathbb R^3.
\tag{S2}
\]

Indeed some two of the three spin labels coincide, and exchanging those particles leaves the argument unchanged while reversing the component's sign. Thus the positive value at total collapse used by the N=2 singlet proof has no N=3 counterpart. At \((0,0,t)\), only components whose first two spins coincide are forced to vanish; opposite-spin components may be nonzero. This distinction is essential in the collision analysis.

Any isolated full-space eigenvalue has multiplicity at least two. Its finite-dimensional eigenspace is invariant under S_z and spin flip; a nonzero S_z eigenvector has a nonzero half-integer eigenvalue, and flipping its spin produces an orthogonal eigenvector at the same energy. A rank-one ground projection therefore cannot describe lithium in the full spin-space.

## 4. A completely specified trial and actual S=1/2 ground spin

For rational \(\kappa>0\) take the normalized hydrogenic orbitals

\[
u_\kappa(x)=(\kappa^3/\pi)^{1/2}e^{-\kappa|x|},
\qquad
v_\kappa(x)=(\kappa^3/(32\pi))^{1/2}(2-\kappa|x|)e^{-\kappa|x|/2}.
\]

They are orthonormal and in H^2. Explicitly the radial norm integrals are
\(4\kappa^3\int_0^\infty r^2e^{-2\kappa r}dr=1\) and
\((\kappa^3/8)\int_0^\infty r^2(2-\kappa r)^2e^{-\kappa r}dr=1\).
The overlap is a nonzero common normalization factor times
\(\int_0^\infty r^2(2-\kappa r)e^{-3\kappa r/2}dr=0\), by the gamma-integral identity. Their weak Hessians have at worst a locally square-integrable inverse-radius term and exponential tails, giving H^2 membership directly. Let

\[
\Phi_\kappa=u_\kappa\uparrow\ \wedge\ u_\kappa\downarrow\ \wedge\ v_\kappa\uparrow,
\]

where the exterior product is the determinant divided by sqrt(3!). Its norm is one. This closed-shell plus one electron state has S=1/2 and S_z=1/2: the total raising operator kills it because raising its sole down-spin orbital produces two identical u-up columns in the determinant. The identity \(S^2=S_-S_++S_z(S_z+1)\) therefore gives \(S^2\Phi_\kappa=(3/4)\Phi_\kappa\). No trial coefficient was inferred from a floating-point eigensolver.

The standard hydrogen spectrum is a continuum dependency: the one-body operator \(-\Delta/2-Z/|x|\) has eigenvalues \(-Z^2/(2k^2)\), spatial multiplicity k^2, and continuum beginning at zero. To spell out the Pauli comparison, write \(h_Z\ge e_1P_1+e_2(I-P_1)\), with \(e_1=-Z^2/2\), \(e_2=-Z^2/8\), and P1 the 1s projection. The total occupation of a rank-r one-body subspace is at most r on a fermionic exterior power, as one sees in an orthonormal wedge basis. Here P1 has spin-space rank two, so summing the one-body inequalities gives \(\sum_i h_Z^{(i)}\ge2e_1+e_2\). Dropping the nonnegative repulsion gives

\[
E_{3,Z}\ge-Z^2-Z^2/8=-9Z^2/8.
\tag{V1}
\]

The kinetic and nuclear expectations in \(\Phi_\kappa\) sum to \(9\kappa^2/8-(9/4)Z\kappa\). To verify the repulsion exactly it suffices by scaling to set \(\kappa=1\). The angular identity is

\[
\int_{S^2}\int_{S^2}\frac{d\omega\,d\nu}{|r\omega-s\nu|}
=\frac{16\pi^2}{\max(r,s)}.
\]

It follows by fixing one direction, integrating \(2\pi\int_{-1}^1(r^2+s^2-2rst)^{-1/2}dt\), and integrating the fixed direction over 4pi. The coincident r=s case follows by integrability or passage to the limit.

Thus J11, J12 and K12 become polynomial-exponential radial double integrals. For i,j nonnegative and a,b positive rational,

\[
\int_0^\infty\int_0^r r^i s^j e^{-ar-bs}\,ds\,dr
=\sum_{k=0}^{i}\frac{i!}{k!a^{i-k+1}}
\frac{(j+k)!}{(a+b)^{j+k+1}}.
\tag{V2}
\]

This is obtained by swapping integrations and integrating \(r^i e^{-ar}\) from s to infinity by parts i times. Split the Coulomb integral into r≥s and s≥r, apply (V2), and obtain

\[
J_{11}=5/8,\qquad J_{12}=17/81,\qquad K_{12}=16/729.
\]

Expanding the normalized determinant, spin orthogonality leaves one 1s–1s direct term, two 1s–2s direct terms, and one same-spin exchange term. Therefore

\[
\langle\Phi_\kappa,H_{3,Z}\Phi_\kappa\rangle
=\frac98\kappa^2-
\left(\frac94Z-\frac{5965}{5832}\right)\kappa.
\tag{V3}
\]

The independent standard-library `Fraction` computation in `check_lithium_rational_v1.py` checks the normalization integrals, zero orbital overlap, all three Coulomb integrals, and the subsequent rational arithmetic. It does not by itself check the angular identity, determinant expansion, spectrum, or variational principle. Its observed result is recorded in `lithium_rational_result_v1.json`; Python 3.14.7, exit status 0. Reproduction, without overwriting the completed result:

```sh
python3 THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/lithium/check_lithium_rational_v1.py
```

At Z=3, choosing \(\kappa=3\) gives \(-6859/972\). Optimizing the quadratic (V3) over positive common charges gives the explicitly rational choice

\[
\kappa=33401/13122,
\qquad
\langle\Phi_\kappa,H_{3,3}\Phi_\kappa\rangle
=-1115626801/153055008.
\]

This proves the upper endpoint displayed at the beginning. The unscreened mean also agrees with Friesecke–Goddard's Table 15, providing a separate primary-literature comparison.

To exclude total spin 3/2, note that its highest-weight component has three up spins and hence a completely antisymmetric spatial factor. Its noninteracting energy is bounded below by the sum of the three lowest *spatial* hydrogenic levels, \(-Z^2/2-Z^2/8-Z^2/8=-3Z^2/4\). Spin-lowering preserves its energy and norm up to a fixed common factor, so this bound holds on the entire quartet sector. Repulsion is nonnegative. At Z=3,

\[
\inf\sigma(H_{3,3}|_{S=3/2})\ge-27/4
>-6859/972\ge E_{3,3},
\]

with rational separation \(149/486\) between the quartet lower bound and the unscreened trial upper bound. The only total-spin sectors for three spin-1/2 particles are 1/2 and 3/2; the ground eigenspace is consequently entirely S=1/2. This proof does not determine L or the number of copies of the spin doublet in that eigenspace.

## 5. Ground binding and what a spectral certificate must still prove

The primary paper Anapolitanos–Lewin, *Compactness of molecular reaction paths in quantum mechanics*, §1.1.1, printed pp.4–5, explicitly uses the antisymmetric spin-1/2 continuum space and H^2 domain. Its HVZ/Zhislin statement gives, for N less than total nuclear charge plus one,

\[
E_N<\min\sigma_{\rm ess}(H_N)=E_{N-1}.
\]

One nucleus with N=Z=3 satisfies this condition. Hence lithium has an isolated finite-multiplicity ground eigenspace below the two-electron lithium-ion threshold \(E_{2,3}\). This is a qualitative established input, not a computed rational gap. [Primary paper](https://publikationen.bibliothek.kit.edu/1000086912/18773460).

The original Zhislin–Sigalov symmetry paper, §1.5, Theorem III, p.840, assumes the corresponding attraction condition and gives infinitely many discrete eigenvalues. The original Russian OCR damages representation subscripts, so no unverified sector-indexed inequality is transcribed here. [Original full text](https://www.mathnet.ru/php/getFT.phtml?jrnid=im&option_lang=eng&paperid=3076&what=fullt).

Three certification distinctions follow.

1. **Degeneracy is allowed by Temple itself.** If a verified rational beta lies strictly above the ground energy and below *every other distinct spectral value*, the usual spectral-measure proof of Temple works with the whole ground eigenspace. Rank one is unnecessary.
2. **The ionization threshold is not a Temple separator.** HVZ describes escape channels and does not exclude excited discrete eigenvalues below that threshold. With such an excited eigenvector as trial, residual zero would certify the wrong energy if the threshold were used as beta. A rational enclosure of \(E_{2,3}\) alone does not solve this issue.
3. **The frozen noninteracting rank-one construction does not transfer.** For three electrons the noninteracting bottom already has rank eight in full spin-space (two filled 1s spin orbitals and one of eight n=2 spin orbitals). Its next level is \(-19Z^2/18\). In S_z=1/2 these multiplicities halve, but remain greater than one. Moreover its infinitely many \(1s^2\,ks\) channels accumulate at \(-Z^2\). No finite-rank projection P can satisfy a free-operator complementary lower bound beta greater than \(-Z^2\): infinitely many orthogonal eigenvectors would otherwise lie below beta. At Z=3 all variational means just proved are above −9. Thus these explicit trials cannot be combined with any such free comparison to obtain the needed separator.

A justified alternative is a block certificate. Let H be this continuum operator, P an orthogonal projection onto a finite-dimensional span contained in D(H), and Q=I−P. Suppose the following **independently certified continuum premises** hold:

\[
PHP\ge aP,\qquad QHQ\ge\beta Q\text{ in form sense},
\qquad\|QHP\|\le\eta,\quad\beta>a.
\tag{C1}
\]

For p=Pf and q=Qf, Cauchy–Schwarz and Young's inequality give

\[
\langle f,Hf\rangle
\ge a\|p\|^2+\beta\|q\|^2-2\eta\|p\|\|q\|
\ge\left(a-\frac{\eta^2}{\beta-a}\right)\|f\|^2.
\]

If a rational u is the Rayleigh upper bound of any normalized vector in P, then

\[
\left[a-\frac{\eta^2}{\beta-a},u\right]
\tag{C2}
\]

encloses the full ground energy. This elementary conditional lemma accommodates a whole multiplet and does not ask which scalar eigenvector a residual optimizer selected. The complement inequality in (C1) is the main unresolved physical obligation; it cannot be read off the finite Ritz matrix. For an orthonormal basis of P, the squared coupling norm is the top eigenvalue of the matrix with entries \(\langle H\phi_i,H\phi_j\rangle\) minus \((PHP)^2\), which uses only D(H), not D(H^2).

## 6. Multiple collisions persist away from total collapse

Let nucleus label 0 have position zero and let labels 1,2,3 be the electrons. On a shell \(1/2\le\rho=(\sum_i|x_i|^2)^{1/2}\le2\), the proper nontrivial collision types, up to electron relabeling, are:

| Collision partition | Representative | Singular internal distances |
|---|---|---|
| One nucleus–electron pair | x1=0; x2,x3 separated from each other and zero | r1 |
| One electron pair | x1=x2≠0; x3 separated | r12 |
| Two disjoint pairs | x1=0; x2=x3≠0 | r1 and r23 |
| Nucleus and two electrons | x1=x2=0; x3≠0 | r1, r2, r12 |
| Three electrons away from nucleus | x1=x2=x3=t≠0 | r12, r13, r23 |
| Total collapse, off this shell | x1=x2=x3=0 | all six |

The list follows by partitioning the four labels into equal-position blocks. It includes all intersections; neighborhoods additionally require nested ratios describing approach to smaller subclusters.

At the specifically requested point \((x_1,x_2,x_3)=(0,0,t_0)\), t0 nonzero, the operator is locally

\[
-\tfrac12(\Delta_1+\Delta_2+\Delta_t)
-3/r_1-3/r_2+1/r_{12}+W(x_1,x_2,t),
\]
\[
W=-3/|t|+1/|t-x_1|+1/|t-x_2|.
\tag{M1}
\]

W has a common analytic neighborhood when t remains close to t0 and x1,x2 are sufficiently small. But the other **three** displayed poles remain. Lifting x1=K(y) clears r1 only; multiplying the equation by \(8|y|^2\) leaves

\[
-24|y|^2/|x_2|+8|y|^2/|K(y)-x_2|,
\]

which are not analytic on a neighborhood of this multiple collision. A second independent KS lift does not repair the electron-pair pole: it creates a coefficient proportional to

\[
\frac{|y_1|^2|y_2|^2}{|K(y_1)-K(y_2)|},
\]

singular even when y1=y2 is nonzero. Hence the exact hypotheses of the frozen isolated-pair operator lemma fail. Its final audit itself explicitly requires all spectator poles to be separated. This is a concrete geometric obstruction, independent of whether that lemma is correct for N=2.

Even disjoint simultaneous pairs would require a new model operator after two lifts. Its highest-order coefficients include products of the two vanishing squared radii, rather than the single Grushin degeneracy treated in the frozen lemma. No analytic-hypoellipticity theorem for that new operator has been proved or invoked here. At the electron-only triple collision there are again three relative-coordinate poles; the Pauli vanishing (S2) does not by itself yield analyticity or factorial bounds.

### Regularity available from primary sources

Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Sørensen, Theorem 1.4, equations (1.8)–(1.13), explicitly excludes **every other** collision from the isolated-pair strata. It supplies analytic-plus-one-distance decompositions there, not at \((0,0,t_0)\). The condition is visible in the definitions of \(\Sigma_k\) and \(\Sigma_{k,\ell}\). [Primary theorem](https://arxiv.org/html/0806.1004).

Their earlier sharp-regularity Theorem 1.1 applies to local many-electron solutions without symmetry assumptions and hence componentwise to the fermionic eigenfunction. In our kinetic convention, the scaling y=2x gives

\[
\Psi=e^{F_1+F_2}\Phi,\qquad\Phi\in C^{1,1}_{\rm loc},
\]
\[
F_1=-Z\sum_i r_i+\tfrac12\sum_{i<j}r_{ij},
\quad
F_2=\frac{Z(2-\pi)}{3\pi}
\sum_{i<j}(x_i\cdot x_j)\log(r_i^2+r_j^2).
\tag{M2}
\]

The quadratic polynomial contributed by log(4) is absorbed into the C1,1 factor. This factorization controls second-order singular structure, not analytic radii or factorial growth. [Primary theorem, pp.3–4](https://arxiv.org/pdf/math-ph/0312060).

An explicit consequence of (M2) illustrates the missing multiple-collision structure. Put \(\rho_{12}=(r_1^2+r_2^2)^{1/2}\) and hold t=t0. The i,j=1,2 logarithm is singular as \(\rho_{12}\to0\), while the logarithms involving t are analytic. If a spin component of \(e^{-F_1}\Psi\) has nonzero value b at (0,0,t0), then on an angular cone away from its pair axes,

\[
\partial_{\rho_{12}}^2(e^{-F_1}\Psi)
=4\frac{Z(2-\pi)}{3\pi}b(\omega_1\cdot\omega_2)
\log\rho_{12}+O(1).
\tag{M3}
\]

To check (M3), differentiate \(\rho_{12}^2\log(\rho_{12}^2)\) twice; its logarithmic coefficient is 4. The C1,1 remainder has bounded radial second derivative and differs from its limiting value by O(rho12). The other factors have bounded derivatives on that cone. The same-spin component used in the scalar sector is forced to have b=0; opposite-spin components are not. We have **not** proved that any actual lithium component has b nonzero. Accordingly (M3) is a conditional singularity test, not an asserted nonvanishing fact or a new counterexample to the actual eigenfunction's regularity. It does show why extraction only at total collapse cannot be assumed to remove all relevant logarithms.

Ammann–Mougel–Nistor, Theorem 1.1, applies to the intersection-closed semilattice generated by the collision subspaces. With

\[
\delta(x)=\min(1,r_1,r_2,r_3,r_{12}/\sqrt2,r_{13}/\sqrt2,r_{23}/\sqrt2),
\]

it gives \(\delta^{|\alpha|}\partial^\alpha\Psi\in L^2\) for each multi-index. Signs and the kinetic constant are covered by constant coefficients in their potential after rewriting the equation as \((\Delta-2V)\Psi=-2E\Psi\). The result handles all intersections, but its statement provides neither a factorial bound in derivative order nor the stronger weight needed for unweighted global H^2 exponential approximation. [Primary theorem, p.3](https://arxiv.org/pdf/2012.13902).

The next analytic target must therefore specify weights for all cluster radii (including rho12 with t separated), derivative directions tangential to each stratum, and their joint uniform constants. Proving estimates only on a shell measured by total rho leaves precisely these inner collisions untreated. A six-distance description also has Gram-determinant constraints and possible orientation/parity information for three vectors; the N=2 octant/perimetric construction is not an unchanged coordinate dictionary. No reduction to a scalar rotation-invariant S state is licensed by the spin result above.

## 7. A justified graph-core alternative, with no rate claimed

An exact proposed **fallback dictionary**, explicitly different from the frozen N=2 dyadic dictionary, is

\[
W_n=T\,\operatorname{span}_{\mathbb C}
\left\{\tfrac12(I-U_{12})\left[x^\alpha e^{-|x|^2}\right]:
\alpha\in\mathbb N_0^9,\ |\alpha|\le n\right\},
\tag{D1}
\]

where U12 exchanges x1,x2 and T is the exact spin reconstruction above. Remove zero and dependent vectors by exact polynomial algebra. The spaces are nested, contained in D(H), and have dimension at most \(\binom{n+9}{9}\). Rational real and imaginary coefficients are dense in each one. Finite Hermite expansions approximate Schwartz functions in their Schwartz seminorms; Schwartz is dense in H^2; the exchange projection and T are bounded on H^2. Thus the union of Wn is **graph dense in the exact ground-energy sector**. The argument establishes convergence without an approximation order versus error bound.

For each fixed rational vector from (D1), its norm and mean are computable. Polynomial-Gaussian factors give explicit Gaussian tails. To handle a Coulomb term one can excise rational tubes around its linear collision subspace, bound the omitted contribution by an explicit polynomial-Gaussian envelope and \(\int_{|y|<h}|y|^{-1}dy=2\pi h^2\), and integrate the smooth remainder on a rational box with derivative bounds. The maximum over the complementary directions of each polynomial-Gaussian envelope is effectively bounded. For squared-action moments, products of two inverse distances are bounded by half the sum of their squares; transverse \(|y|^{-2}\) has integral \(4\pi h\). These observations give finite error-controlled algorithms, with no polynomial bit-cost assertion.

Enumerating nonzero rational vectors in (D1), computing increasingly accurate rational upper bounds on their Rayleigh quotients, and taking running minima gives a computable decreasing rational sequence converging to E3,3. Density proves convergence, but supplies no effective modulus. This establishes upper semicomputability by a concrete continuum core; it does **not** give two-sided requested-precision computability, a verified executable solver, termination of a Temple loop, or polynomial precision cost. Those conclusions require a certified lower mechanism such as (C1), plus quantitative approximation and moment-cost bounds.

## 8. Obligations and status ledger

| Item | Status supported here | Exact next obligation |
|---|---|---|
| Actual fermionic H² domain and graph equivalence | Paper proof using Hardy and Kato–Rellich | Formalize these analytic inputs in Lean |
| Full ground-energy reduction to S_z=1/2 | Explicit isometry proof | Formalize spin/permutation maps and domain commutation |
| Lithium ground spin S=1/2 | Paper spectral/variational proof; rational integrals independently checked | Formalize hydrogen spectrum and quartet comparison |
| Coarse rational energy enclosure | Explicit continuum trial plus free comparison | It is not an arbitrary-precision algorithm |
| Ground binding below E2,3 | Established HVZ/Zhislin application | Produce rational threshold and usable ground-cluster separator if certification needs them |
| Ground orbital L=0 and exact multiplicity two | Not established in this audit | Prove sector comparison or recover an applicable primary theorem at Z=3 |
| Isolated pair regularity | Established primary theorem | Quantitative uniformity only where spectator distances stay positive |
| All multiple-collision weighted analyticity | Unresolved | New intersecting-cluster operator estimates with factorial constants |
| Global H² approximation at an explicit fast rate | Unresolved | Cluster-aware dictionary, weak-derivative treatment, tails and one global witness |
| Rational residual/complement certificate | Conditional block lemma proved on paper | Discharge the continuum complement inequality and certify moments |
| Terminating lithium enclosure algorithm | Not delivered | A lower-bound procedure with independently proved convergence |
| Fixed-N polynomial precision cost | Not established | Rate, coefficient size, conditioning, moment bit cost, and certified selection |
| Lean verification | None produced by this subtask | No paper statement above is labeled Lean-verified |

The relevant Friesecke–Goddard ground-symmetry theorem is explicitly for sufficiently large Z, so it cannot be used to settle L=0 at Z=3. Its Table 15 exact Slater mean matches the independent arithmetic above. [Primary paper, Theorem 3.1 and Table 15](https://wrap.warwick.ac.uk/id/eprint/2209/1/WRAP_Friesecke_Explicit_large.pdf). Failure to locate a theorem at Z=3 in this bounded search is not evidence of novelty or of its nonexistence.

No claim in this file is upgraded based on agreement between agents. The evidential separation is: primary theorems with checked applicability; explicit new paper deductions from those theorems; exact rational identities executed locally; and the unresolved obligations listed above. This version should be preserved after sealing; subsequent corrections belong in a new version or append-only erratum.
