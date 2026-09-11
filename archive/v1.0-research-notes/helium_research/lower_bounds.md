> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Helium and molecular energy lower bounds: primary-source audit

Audit date: 9 September 2026. This is a targeted survey, followed by a paper proof of a useful helium certificate. **No continuum theorem or literature computation in this file is Lean checked.** A mathematical inequality, a floating-point evaluation of it, a verified interval computation, and a proof checked by Lean are different deliverables.

## Research first: what the sources establish

The entries below distinguish papers actually read from bibliographic leads whose primary full text was inaccessible. The recent search window was 9 September 2024–9 September 2026; older sources supply the foundational theorems and helium comparisons. Journal issue dates and arXiv version dates are used, rather than search-engine crawl dates.

| Source and precise location | Access and result | Status and remaining certification obligations |
|---|---|---|
| Temple, *The theory of Rayleigh’s principle as applied to continuous systems*, Proc. Roy. Soc. A **119**, 276–293 (1928), [DOI 10.1098/rspa.1928.0098](https://doi.org/10.1098/rspa.1928.0098) | Original 18-page scan retrieved from a [mirror](https://scispace.com/pdf/the-theory-of-rayleigh-s-principle-as-applied-to-continuous-2l19ezrbla.pdf) using Chrome after publisher and direct HTTP fetches failed. §§1, 5, 7–8 read; formulas on p.292 visually checked. §5, pp.283–285, specifies a fourth-order self-adjoint differential problem on a finite interval, regular coefficients, boundary identities, and an invertible positive Green operator. §7 constructs successive Green-operator iterates. Equations (8.1)–(8.4), p.292, bound the lowest-eigenvalue error using their Rayleigh ratios, the squared Green-kernel integral, and eigenvalue multiplicities. | **PROVEN (paper proof only)** under that differential-system setup; this is not an automatic whole-space Coulomb certificate. The modern single-trial variance statement appears in Harrell’s Theorem 1 and is independently proved below. The archived scan and extracted text are `helium_research/sources/temple_1928.pdf` and `.txt`. |
| Kato, *On the Upper and Lower Bounds of Eigenvalues*, JPSJ **4**, 334–339 (1949), [DOI 10.1143/JPSJ.4.334](https://doi.org/10.1143/JPSJ.4.334); *Upper and Lower Bounds of Eigenvalues*, Phys. Rev. **77**, 413 (1950), [DOI 10.1103/PhysRev.77.413](https://doi.org/10.1103/PhysRev.77.413) | Primary publisher metadata located; J-STAGE PDF redirected to authentication and APS full text was unavailable. | **Original full texts not read.** These are eigenvalue-bound sources, not evidence for a modern decimal enclosure. |
| Kato, *On the Existence of Solutions of the Helium Wave Equation*, Trans. AMS **70**, 212–218 (1951), [DOI 10.1090/S0002-9947-1951-0041011-1](https://doi.org/10.1090/S0002-9947-1951-0041011-1) | Bibliographic identification checked against the citation in Bazley–Fox’s primary paper; AMS PDF returned HTTP 403. | **Original not read.** This existence paper must not be conflated with the 1949–1950 eigenvalue-bound papers or with a computational helium energy enclosure. |
| D. H. Weinstein, *Modified Ritz Method*, PNAS **20**, 529–532 (1934), [DOI 10.1073/pnas.20.9.529](https://doi.org/10.1073/pnas.20.9.529) | **All four original scan pages read** through the [PMC article’s page images](https://pmc.ncbi.nlm.nih.gov/articles/PMC1076472/?page=-1) in Chrome, after PDF fetches failed. Equations (4)–(7), pp.530–531, enclose the eigenvalue nearest the chosen center. Those pages explicitly warn that the method does not identify the level’s order. §3 discusses difficulties with formally interchanging H² expressions and divergent expansions. | **PROVEN (paper proof only)** in its stated eigenfunction-expansion setting. It supports a nearby-eigenvalue enclosure, not an automatic ground/first-excited index. The modern spectral-measure statement proved below also covers continuous spectrum. |
| Harrell, *Generalizations of Temple’s Inequality*, Proc. AMS **69**, 271–276 (1978), [DOI 10.2307/2042610](https://doi.org/10.2307/2042610) | Author-uploaded primary text on [ResearchGate](https://www.researchgate.net/publication/243059969_Generalizations_of_Temple%27s_Inequality) read. Theorem 1, p.272, states Temple for a normalized vector in the operator domain. Theorem 2 treats an isolated eigenvalue; Lemma 4, p.276, controls eigenspace overlap. | **PROVEN (paper proof only).** Spectral separation and the strong residual remain inputs. This supplies an accessible modern primary theorem statement; the Kato originals remain unread. |
| Boulton–Hobiny, *On the quality of complementary bounds for eigenvalues*, [arXiv:1311.5181v2](https://arxiv.org/abs/1311.5181), 11 August 2014 | Full PDF read. Definitions pp.2–3 use trial vectors in D(A) and matrices of ⟨u,v⟩, ⟨Au,v⟩, ⟨Au,Av⟩. Lemmas 2.1/2.4 give complementary Lehmann–Maehly–Goerisch bounds; Remark 2.5, p.6, explicitly requires prior spectral-count information for correct indexing. Theorem 4.4 gives convergence in terms of trial-space approximation. | **PROVEN (paper proof only),** under the paper’s semiboundedness and **compact-resolvent** assumptions. Whole-space molecular Coulomb operators do not have compact resolvent. Its applications are one-dimensional oscillators, not helium or H₂. The original Lehmann/Maehly papers were not independently retrieved. |
| Bazley, *Lower Bounds for Eigenvalues with Application to the Helium Atom*, PNAS **45**, 850–853 (1959), [DOI 10.1073/pnas.45.6.850](https://doi.org/10.1073/pnas.45.6.850); Phys. Rev. **120**, 144–149 (1960), [DOI 10.1103/PhysRev.120.144](https://doi.org/10.1103/PhysRev.120.144) | Primary metadata/abstract located, full texts not retrieved. The 1960 abstract reports an excited-level lower bound −2.1655 and a combined ground lower bound −2.9037474. | **Abstract claims, not independently audited proofs or computations.** The symmetry and numerical details must be checked before transplanting these separators. |
| Bazley–Fox, *Truncations in the method of intermediate problems for lower bounds to eigenvalues*, J. Res. NBS **65B**, 105–111 (1961), [primary NIST PDF](https://nvlpubs.nist.gov/nistpubs/jres/65B/jresv65Bn2p105_A1b.pdf) | Full text read. §2 starts with a semibounded self-adjoint operator A=A⁰+A′, known base spectral resolution and positive A′; continuous spectrum is allowed. §§3–4 replace the correction by explicitly solvable finite intermediate problems; p.110 proves convergence under stated operator hypotheses. | **PROVEN (paper proof only).** This is a substantive route to lower bounds, not ordinary Galerkin projection. It gives no general polynomial bit-cost theorem or interval-certified helium table. A DOI was not verified for this particular NIST paper. |

### Helium calculations: precision and proof are separate

**Nakashima–Nakatsuji (2008).** The full four-page author PDF of [DOI 10.1103/PhysRevLett.101.240406](https://doi.org/10.1103/PhysRevLett.101.240406), [available here](https://qcri.or.jp/lab/wp-content/uploads/2011/07/p358.pdf), was read. Equations (3)–(7) use variance, Weinstein, and modified Temple; the separator is obtained from an approximate excited state of the same symmetry. At order 27, dimension 22,709, p.4 reports variance 1.293955798978967642728022186398914855×10⁻³² and lower energy −2.903724377034119598311159245194421785. The paper claims 32 guaranteed digits. It does not provide directed-rounding enclosures or a rounding-error budget, nor an explicit proof that the excited-state residual identifies the required spectral index. Its bold upper-energy digits partly use convergence-ratio judgments. **Status: extraordinary reported numerical precision with paper inequalities; not a reproduced interval certificate or Lean proof.** The analytic separator proved below repairs the indexing requirement if the trial moments are certified. Sampled local-energy slices and small L² variance do not prove a uniform pointwise error bound.

**Ireland et al. (2021/2022).** [DOI 10.1021/acsphyschemau.1c00018](https://doi.org/10.1021/acsphyschemau.1c00018), ACS Phys. Chem. Au **2**, 23–37, was read as primary full-text [Europe PMC XML](https://www.ebi.ac.uk/europepmc/webservices/rest/PMC8796283/fullTextXML). §3 evaluates explicitly correlated Gaussian H² matrix elements in quadruple-precision Fortran. Results/Table 2 explicitly construct estimated excited lower bounds by subtracting δ from literature variational upper bounds; for helium δ≈10⁻¹⁰ Hartree. The authors distinguish estimated from true bounds. Their Pollak–Martinazzo procedure additionally requires conditions on auxiliary roots xⱼ(E₀), whose verification is discussed in the results and conclusion. Tables 1/3 report helium Temple and PM values; the latter improve strongly after variance/basis optimization. **Status: EMPIRICAL computations of conditional lower-bound formulas.** Neither sensitivity tests nor a chosen δ proves the separator; no directed-rounding certificate is supplied. This remains useful primary evidence for variance-aware trial construction.

**Ronto et al. (2023).** [arXiv:2301.02827](https://arxiv.org/abs/2301.02827), [DOI 10.1103/PhysRevA.107.012204](https://doi.org/10.1103/PhysRevA.107.012204), full ten-page PDF read. §II, p.3, conditions the PM construction on auxiliary-root ordering; §III.A, p.4, explains that naive optimization can give a value above the target eigenvalue. The multistate ECG strategy improves Li/Be results. §III.B.1, pp.7–8, reports a helium failure of the required ordering and uses known reference energies to arrange a successful helium trial. §III uses double/quadruple precision. **Status: EMPIRICAL lower-bound estimates based on paper theory; not an interval or Lean certificate.** Accurate excited-state approximation does not automatically prove the needed root ordering or a global spectral separator.

### H₂ and H₂⁺: keep the electron count and normalization explicit

**Jennings (1967), neutral H₂.** [DOI 10.1063/1.1841057](https://doi.org/10.1063/1.1841057), JCP **46**, 2442–2443, [full primary university copy](https://researchportal.murdoch.edu.au/view/pdfCoverPage?download=true&filePid=13136800100007891&instCode=61MUN_INST) read. Equation (1) uses Miller’s intermediate-operator determinant and explicitly demands an unperturbed spectral separator. It uses approximated H₂⁺ orbitals and five-dimensional Gaussian quadrature, six nodes per dimension, reporting three-digit accuracy. Table I spans H₂ separations 0.6–4 bohr and dissociation. At 1.4 bohr, the reported total-energy lower value −1.214 differs from the listed upper −1.1745 by 39.5 mHa. **Status: historical continuum lower-bound calculation with numerical integration; no certified quadrature remainder or rounding proof in the two pages.** Its energy convention includes the nuclear repulsion, so it is not directly the electronic H in the question. This rules out saying that continuum H₂ lower-bound calculations do not exist; it does not establish a modern verified enclosure.

**Liu, May 2026.** [arXiv:2605.05177v1](https://arxiv.org/abs/2605.05177), *Explicit Two-Sided Eigenvalue Bounds for Schrödinger Operators with Singular Potentials via Finite Element Method*, full HTML read. It treats one-electron problems in two/three spatial dimensions, including H and H₂⁺, using enriched nonconforming finite elements, explicit inequalities, and domain-truncation estimates. The abstract expressly leaves IEEE/interval-safe implementation to separate work. **Status: paper lower-bound analysis plus ordinary numerical examples; not an interval-certified helium or neutral H₂ computation.** Spatial dimension in this paper is not electron count.

**Liu, August 2026.** [arXiv:2608.25760v1](https://arxiv.org/abs/2608.25760), *From estimate to proof: certified ground-state energy bounds for singular Schrödinger operators*, full HTML and relevant supplementary proofs read. §6 reports an IntervalArithmetic.jl enclosure [−0.5514436010,−0.5509672618] for −Δ−1/|x−a₁|−1/|x−a₂|, a₁,₂=(∓2,0,0). Theorem 1 supplies whole-space Dirichlet–Neumann bracketing, Theorems 2/3 projection and Lehmann–Goerisch bounds; SI §§6–9 specify the separator, coercivity bootstrap, residual-defect certification, and integral remainders. The headline box result is labelled verified, whereas Gaussian results are explicitly floating point. **Status: author-reported computer-assisted certificate in a new preprint, not independently reproduced or Lean checked here.** Code repositories are [schrodinger](https://github.com/xfliu/schrodinger) and [veigs](https://github.com/xfliu/veigs); neither was run. Scope is H₂⁺, not He/H₂, with no polynomial-in-electron-count theorem. Priority claims such as “first” were not independently verified.

The normalization conversion in that last example is elementary: put x=2r and transform the L² norm unitarily. Its operator becomes one-half of the usual Hartree electronic H₂⁺ operator with nuclei at r=(∓1,0,0), hence separation 2 bohr. Doubling the displayed endpoints gives [−1.1028872020,−1.1019345236] Hartree, width 0.9526784 mHa. Adding the nuclear-repulsion constant 1/2 would instead give total Born–Oppenheimer energies. These are unit conversions of an author-reported interval, not a computation reproduced in this project.

### What has actually been discharged?

| Requirement | A rigorous Temple/Lehmann application needs | What the audited evidence supplies |
|---|---|---|
| Continuum operator | Hilbert space, self-adjoint realization, correct particle statistics | Precisely defined below for helium; standard analytic facts remain paper mathematics. A finite matrix alone does not define the whole-space problem. |
| Trial domain | ψ∈D(H), equivalently spatial H² here, for the strong residual | Gaussians satisfy this. Generic H¹ finite elements do not; Goerisch’s weak-form/flux formulation has different, explicit requirements. |
| Second moment | Certified ∥Hψ∥², or a certified upper bound for a residual | High-precision variances appear in helium papers; directed rounding was not verified there. Interval quadrature/remainder and defect methods are specified in the August 2026 one-electron preprint. |
| Spectral separator | A proven exclusion of every unwanted lower level | β=−5/2 is proved below for full spin-fermionic helium. A second Ritz value, guessed pole, or residual near some level is insufficient alone. |
| Whole space | Global trial integrals or certified box/exterior comparison | Global atomic trial functions avoid artificial boundaries. Dirichlet–Neumann bracketing in the August paper explicitly controls truncation. |
| Arithmetic | Directed rounding, rational bounds, or proved numerical error bounds in every load-bearing quantity | No literature computation was rerun here; only the August preprint explicitly supplies an interval pipeline among the examples read. |
| Complexity | Explicit basis size, parameter bits, quadrature cost, spectral separation, and optimization guarantees as ε varies | No surveyed paper supplies the user’s polynomial-in-N-and-log(1/ε) result. A convergence experiment does not supply these bounds. |
| Geometry | A specified atom or nuclear coordinates; uniform constants if a family is claimed | Helium here is a single fixed nucleus. Jennings samples H₂ geometries; Liu fixes an H₂⁺ geometry. None implies uniform neutral-molecule certification at all stretched geometries. |

The strongest unresolved gap exposed by this audit is a **fully quantitative continuum approximation and certification theorem**, including coefficient bit sizes and certified moments or form bounds, that turns the observed convergence of useful correlated trial families into an algorithm with a proved precision-dependent cost. Existence of good approximations, successful optimization, and an abstract residual inequality discharge different parts of that task.

## Paper proof: a global spectral separator for helium

Let X=ℝ³×{↑,↓}, with Lebesgue measure times counting measure, and let

\[
\mathcal H=\bigwedge^2L^2(X;\mathbb C)
\]

be the closed subspace of square-integrable functions antisymmetric under simultaneous exchange of spatial and spin coordinates. The nucleus has infinite mass, charge Z=2, and position 0. There is no nuclear-nuclear constant. Set

\[
H=-\tfrac12(\Delta_1+\Delta_2)-2/r_1-2/r_2+1/r_{12},
\qquad D(H)=H^2(\mathbb R^6;\mathbb C^4)\cap\mathcal H.
\]

Here H² denotes the Sobolev space, not the square of H. Hardy’s inequality, applied in each relative three-dimensional variable, makes each Coulomb multiplication infinitesimally bounded relative to the free Laplacian. Kato–Rellich therefore makes this a semibounded self-adjoint operator on the stated domain; its closed form domain is H¹∩𝓗. These standard continuum assertions, detailed in `research/analytic.md`, are paper mathematics in this project.

**Theorem 1 (helium separator).** H has exactly one eigenvalue, counting multiplicity, below −5/2. It is the ground energy E₀, and

\[
\sigma(H)\subset\{E_0\}\cup[-5/2,\infty).
\]

**Proof.** The hydrogenic operator h=−Δ/2−2/r on L²(ℝ³) has ground energy −2, ground orbital φ(r)=(8/π)¹ᐟ²e⁻²ʳ, and remaining spectrum bounded below by −1/2. This is the standard exact one-electron Coulomb spectrum −2/n², with continuous spectrum [0,∞). On L²(X), the ground orbital times the two spin functions spans a rank-two spectral subspace P. Thus

\[
h\ge -2P-\tfrac12(I-P).
\]

Consider H⁰=h₁+h₂ on the fermionic space. The subspace in which both electrons occupy P is ∧²P and has dimension one; let its projection be P₀. Its energy is −4. On its orthogonal complement at least one electron lies outside P. The sector with one electron outside has lower bound −2−1/2=−5/2; with both outside the lower bound is −1. This follows by decomposing the tensor product with the commuting projections P₁ and P₂ and then restricting to the exchange-antisymmetric subspace. Consequently, as quadratic forms,

\[
H\ge H^0\ge -4P_0-\tfrac52(I-P_0).
\tag{1}
\]

If the spectral projection Q=1_{(−∞,−5/2)}(H) had dimension at least two, its range would contain a nonzero vector u orthogonal to P₀. Semiboundedness ensures every vector in this spectral subspace belongs to D(H), since its spectral support is bounded. Equation (1) gives ⟨u,Hu⟩≥−(5/2)∥u∥². The spectral theorem instead gives a strict reverse inequality: the positive function −5/2−λ has strictly positive integral against the nonzero spectral measure of u. This is a contradiction. Thus rank Q≤1.

Q is nonzero. Use the normalized determinant φ↑∧φ↓. Its expectation for H⁰ is −4 and its repulsion expectation is 5Z/8=5/4 at Z=2, giving mean −11/4<−5/2. For completeness, angular integration of 1/|r−s| for spherical densities gives 1/max(r,s); with radial probability density 4Z³r²e⁻²ᶻʳ the repulsion integral is

\[
32Z^6\int_0^\infty r e^{-2Zr}
 \int_0^r s^2e^{-2Zs}\,ds\,dr
=32Z^6\int_0^\infty s^2e^{-4Zs}
 \left(\frac{s}{2Z}+\frac1{4Z^2}\right)ds
=\frac{5Z}{8}.
\]

If Q were zero every normalized trial mean would be at least −5/2, contradicting −11/4. A nonzero rank-one reducing spectral subspace is an eigenspace. Everything outside it is at least −5/2, proving existence, uniqueness, and the claimed separation. ∎

This argument uses **fermionic spin statistics**: the two spin states permit precisely one 1s² determinant. Omitting antisymmetry would change its multiplicity argument. It neither assumes a singlet-sector energy ordering nor estimates the first excited helium energy numerically. HVZ would separately identify the essential threshold as −2; it is not needed in the rank-one proof above.

## Paper proof: the exact certificate and its inputs

**Theorem 2 (Temple certificate).** Suppose A is a semibounded self-adjoint operator with spectrum contained in {E₀}∪[β,∞), where E₀<β is its ground eigenvalue. Let ψ∈D(A), ∥ψ∥=1, and define

\[
m=\langle\psi,A\psi\rangle<\beta,
\qquad v=\|(A-m)\psi\|^2=\|A\psi\|^2-m^2.
\]

Then

\[
m-\frac{v}{\beta-m}\le E_0\le m.
\tag{2}
\]

**Proof.** Let μψ be ψ’s scalar spectral probability measure. The support condition implies (λ−E₀)(λ−β)≥0 on its support. The second moment is finite because ψ∈D(A), so integration gives

\[
0\le\int(\lambda-E_0)(\lambda-\beta)\,d\mu_\psi
=v+(m-E_0)(m-\beta).
\]

Since β−m>0, rearrangement gives the lower bound in (2). The upper bound follows by integrating λ≥E₀. ∎

For helium, Theorem 1 supplies β=−5/2. Thus any explicit normalized helium trial in H² with a certified mean below −5/2 and certified variance gives a continuum enclosure. There is no finite-basis completeness assumption in this implication.

**Corollary (interval-safe form).** If certified bounds satisfy

\[
m_-\le m\le m_+<\beta,\qquad 0\le v\le v_+,
\]

then

\[
m_- -\frac{v_+}{\beta-m_+}\le E_0\le m_+.
\tag{3}
\]

Indeed v/(β−m)≤v₊/(β−m₊), and m≥m₋. This termwise argument avoids an unjustified monotonicity assertion about the entire Temple expression. For an unnormalized trial f, its exact norm S=∥f∥²>0, energy numerator K=⟨f,Hf⟩, and second moment Q=∥Hf∥² give the equivalent exact lower bound (βK−Q)/(βS−K), provided βS−K>0. Interval arithmetic must verify this denominator’s positivity and enclose all three integrals.

**Why an unindexed Weinstein residual is insufficient.** The spectral theorem gives dist(m,σ(A))≤∥(A−m)ψ∥. Otherwise the integral of (λ−m)² would be larger than that residual squared. This identifies a nearby spectral point, not the ground state or the first excited state. For example A=diag(0,10), ψ=(0,1) has m=10 and zero residual; m−0=10 is not a ground lower bound. An eigenvalue-index or overlap hypothesis is indispensable when using such a residual as an excited-level lower bound.

**The domain distinction.** The second moment in these theorems is ∥Hψ∥². It requires ψ∈D(H), spatial H² here. Writing it as ⟨ψ,H²ψ⟩ is harmless only if understood as the quadratic form of H²; a literal operator product requires ψ∈D(H²), a stronger condition. Finite Gaussian sums are Schwartz functions and belong to D(H), despite Hψ containing integrable Coulomb singularities. A radial Slater exponential has weak second derivatives behaving as 1/r; their squares are locally integrable in three relative dimensions. Particular correlated Slater/polynomial combinations can be checked similarly. Negative powers and logarithmic terms require their own local integrability checks, especially at simultaneous coalescences. A generic continuous piecewise-linear finite-element trial lies only in H¹ and has distributional second derivatives on element interfaces; its strong residual cannot be silently used in (2).

**Bounded observables.** With a certified interval L≤E₀≤U<β and trial mean m≤U, let p=|⟨ψ₀,ψ⟩|². Spectral separation gives

\[
1-p\le\frac{m-E_0}{\beta-E_0}
\le\frac{U-L}{\beta-U}.
\]

Choosing the ground-state phase makes ∥ψ−ψ₀∥²=2(1−√p)≤2(1−p). For every bounded operator B, expanding the difference of its expectations and using Cauchy–Schwarz gives

\[
|\langle\psi,B\psi\rangle-\langle\psi_0,B\psi_0\rangle|
\le2\sqrt2\,\|B\|\sqrt{\frac{U-L}{\beta-U}}.
\]

Unbounded observables need additional domain and moment estimates; an energy interval alone does not certify all observables.

## Explicit boundary of the result

**PROVEN (Lean checked):** none of the continuum statements in this file.

**PROVEN (paper proof only):** Theorems 1–2 and the corollaries, using the standard exact hydrogen spectrum and Coulomb self-adjointness facts explicitly identified above. The older abstract spectral methods have their own source hypotheses.

**EMPIRICAL:** the surveyed high-precision helium and historical H₂ numerical evaluations; the August 2026 preprint’s claimed interval computation is reported with its stronger author-stated status, but was not independently reproduced or formally verified here.

**CONJECTURED/OPEN here:** a uniform, explicit bit-cost theorem closing the approximation-to-certificate step. Neither this survey nor the separator proof is an arbitrary-precision algorithm with the cost requested in parts (b) or (c).

Points at which a shortcut was rejected: substituting a second Ritz energy for a lower separator; equating decimal agreement with directed rounding; using an unindexed residual as a particular excited eigenvalue; writing H² without distinguishing operator and form domains; treating spatial dimension as electron count; mixing electronic and total energies; replacing whole space by a box without an exterior certificate; importing a compact-resolvent theorem unchanged into a molecular operator; asserting the nonexistence of rigorous H₂ work from a failed search; and treating a new preprint’s own certification or priority claim as independently audited fact.

The next precise theorem to prove or refute is: **for fixed helium H and a fully specified constructive correlated trial family, there is an explicit polynomial P such that for every positive integer p one can produce, within P(p) bit operations, a finite H² trial and rational certified enclosures for S, K, Q which, with β=−5/2 in (3), enclose E₀ in an interval of width at most 2⁻ᵖ.** The definition of the trial family, coefficient bit bounds, moment algorithms, and every error constant belong in that theorem; omitting them would repeat the gap this audit isolates.
