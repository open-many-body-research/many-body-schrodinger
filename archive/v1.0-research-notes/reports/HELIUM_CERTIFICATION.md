> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Two-electron certification: surveyed boundary, conditional algorithm, and executed helium certificate

9 September 2026. All energies are nonrelativistic Hartree energies with fixed, infinite-mass nuclei. Nuclear repulsion is excluded unless explicitly stated. This continues the two-electron target in [the preceding report](NOGO_AND_PIVOT.md); it does not repeat the Gaussian reduction.

**Result and status.** The finite-dimensional Hermitian Temple inequality is **PROVEN (Lean)**. The continuum helium separator and use of Temple are **PROVEN (paper proof only)**, with a separately executed rational arithmetic certificate reported below. The uniform polynomial-bit two-electron algorithm remains **CONJECTURED**: its complete conditional skeleton has one named OPEN analytic approximation lemma and several explicitly labelled elementary implementation obligations. Neither a convergence experiment nor the helium certificate supplies that missing lemma.

## 1. Targeted survey, with the hypotheses kept separate

The full primary-source reading records, theorem/page locations, access failures, and distinctions between analysis and numerical evaluation are in:

- [Lower-bound methods and helium/H₂ enclosures](helium_research/lower_bounds.md).
- [Hylleraas convergence and hp approximation](helium_research/approximation.md).
- [Coulomb regularity and collision structure](helium_research/regularity.md).
- [Successors, Gaussian approximation, and precise scope corrections](helium_research/hp_successors.md).

The requirements against which the sources were checked are: the correct continuum operator and trial domain; a certified lower-energy separator or an effective global approximation bound; explicit constants uniform over the promised geometry class; and a bit-cost bound covering dictionary construction, integration, conditioning, and the finite solve. No single source read discharges all of them.

**Temple and Kato.** Temple's original [1928 paper, DOI 10.1098/rspa.1928.0098](https://doi.org/10.1098/rspa.1928.0098), especially §§5, 7–8 and p.292, was read from the original scan. Its regular finite-interval differential-system and positive Green-operator hypotheses are narrower than a whole-space molecular application. The modern single-trial theorem is stated in Harrell's Theorem 1, [DOI 10.2307/2042610](https://doi.org/10.2307/2042610), and independently proved in §3 below. It supplies the explicit posterior constant (1/(\beta-m)), assuming a trial in (D(H)), its certified second moment, and a valid separator. It supplies no approximation rate or uniform geometry cost.

Kato's [1949 JPSJ paper, DOI 10.1143/JPSJ.4.334](https://doi.org/10.1143/JPSJ.4.334), [1950 Physical Review paper, DOI 10.1103/PhysRev.77.413](https://doi.org/10.1103/PhysRev.77.413), and [1951 existence paper, DOI 10.1090/S0002-9947-1951-0041011-1](https://doi.org/10.1090/S0002-9947-1951-0041011-1) were located, but their original full texts remained inaccessible after publisher and repository attempts. **They were not read and are not counted as discharged hypotheses.** The 1951 existence paper must not be described as the same result as the 1949–1950 eigenvalue bounds. This part of the requested primary reading remains incomplete; an accessible modern theorem and an independent proof support the certificate instead.

**Weinstein and Lehmann–Maehly.** All four original pages of Weinstein's [1934 paper, DOI 10.1073/pnas.20.9.529](https://doi.org/10.1073/pnas.20.9.529) were read. Its residual interval locates a nearby eigenvalue; pp.530–531 explicitly do not identify its order. Boulton–Hobiny, [arXiv:1311.5181v2](https://arxiv.org/abs/1311.5181), give operator-domain complementary Lehmann–Maehly–Goerisch bounds and approximation estimates. Their compact-resolvent setting and required spectral-count information are explicit; neither automatically applies to the whole molecular spectrum. The original Lehmann/Maehly papers were not independently retrieved. These methods supply conditional lower-certificate formulas, not a geometry-uniform certificate generator or polynomial bit bound.

**Hylleraas expansions and convergence.** Klahn–Bingel I and II, [DOI 10.1007/BF00548026](https://doi.org/10.1007/BF00548026) and [10.1007/BF00548027](https://doi.org/10.1007/BF00548027), were verified through primary abstracts; their full texts were inaccessible. The first distinguishes L² completeness from energy convergence; the second advertises a Hylleraas convergence theorem. Neither abstract verifies the effective H¹ or graph-norm rate needed here. Hill's [1985 paper, DOI 10.1063/1.449481](https://doi.org/10.1063/1.449481), was likewise accessible only through its detailed primary abstract: its partial-wave increments have inverse powers of angular momentum, with coefficients involving the unknown coalescence wavefunction. This is not an exponential theorem in the total Hylleraas polynomial degree used below. The full text of Goddard, [DOI 10.1137/080727956](https://doi.org/10.1137/080727956), makes the distinction precise: its (L^{-3}) energy asymptotic uses regularity assumptions and an angular truncation retaining infinite radial freedom. It does not bound the cost of a fully finite computation. Hill's [1995 scale-parameter paper, DOI 10.1103/PhysRevA.51.4433](https://doi.org/10.1103/PhysRevA.51.4433), was also only abstract-verified. No inaccessible paper is used to claim an explicit convergence constant.

**Coulomb regularity.** Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Sørensen, [math-ph/0312060; DOI 10.1007/s00220-004-1257-6](https://arxiv.org/abs/math-ph/0312060), prove an explicit cusp/logarithmic factorization with a (C^{1,1}) remainder, including triple collisions. It is not a global analytic remainder. Their [arXiv:0806.1004; DOI 10.1007/s00220-008-0664-5](https://arxiv.org/abs/0806.1004), Theorem 1.4, gives a local analytic-plus-distance-times-analytic decomposition near an isolated pair collision, excluding simultaneous collisions. Fournais–Sørensen, [arXiv:1803.03495](https://arxiv.org/abs/1803.03495), and Ammann–Mougel–Nistor, [arXiv:2012.13902; DOI 10.1007/s11005-023-01648-0](https://arxiv.org/abs/2012.13902), give weighted derivative/regularity results. These justify important structural hypotheses and the need to treat collision strata and infinity. All-order smoothness alone does not provide factorial-growth bounds with computable constants, a stable finite dictionary, or bit complexity uniform in geometry.

**hp and Gaussian approximation.** The audited Flad literature must be attributed and scoped carefully. Flad–Hackbusch–Schneider [DOI 10.1051/m2an:2006007](https://doi.org/10.1051/m2an:2006007) concerns Hartree–Fock/Kohn–Sham orbital approximation; their [DOI 10.1051/m2an:2007016](https://doi.org/10.1051/m2an:2007016) treats a two-particle Jastrow/hybrid-wavelet setting on a bounded domain with regularity assumptions. Flad–Schneider–**Schulze**, [DOI 10.1002/mma.1021](https://doi.org/10.1002/mma.1021), is a Hartree–Fock asymptotic paper, not a full correlated electronic hp theorem by Schwab. Feischl–Schwab, [DOI 10.1007/s00211-019-01085-z](https://doi.org/10.1007/s00211-019-01085-z), prove exponential hp approximation of weighted-Gevrey functions with isolated point singularities on bounded two/three-dimensional domains; for analytic order the error is of type (C\exp[-b n^{1/(d+1)}]). The hypotheses do not describe the intersecting three-codimensional collision sets in six-dimensional helium configuration space. Maday–Marcati, [arXiv:1912.07483](https://arxiv.org/abs/1912.07483), also works in a different nonlinear, lower-dimensional setting.

Chernov–von Petersdorff–Schwab, [DOI 10.1051/m2an/2010061](https://doi.org/10.1051/m2an/2010061), provide exponential singular quadrature under weighted-Gevrey assumptions, but counting function evaluations does not count certified bits. Scholz–Yserentant, [arXiv:1612.00360; DOI 10.1007/s00211-016-0856-4](https://arxiv.org/abs/1612.00360), preserve an assumed algebraic Gaussian approximation rate of a smoothed eigenfunction; that does not construct the uniform exponential approximation requested here. Recent Barron/weighted regularity work, including [arXiv:2502.17950](https://arxiv.org/abs/2502.17950) and [arXiv:2608.22252](https://arxiv.org/abs/2608.22252), was checked and does not fill that gap. The detailed reading records explain the constants and geometry dependencies of each result.

**Existing energy enclosures.** Bazley–Fox's [1961 primary NIST paper](https://nvlpubs.nist.gov/nistpubs/jres/65B/jresv65Bn2p105_A1b.pdf) proves an intermediate-operator lower-bound method allowing continuous spectrum, with convergence under its hypotheses; no DOI was verified for that paper. Nakashima–Nakatsuji, [DOI 10.1103/PhysRevLett.101.240406](https://doi.org/10.1103/PhysRevLett.101.240406), report 32 guaranteed helium digits using variance and modified Temple, but the paper supplies neither directed-rounding arithmetic nor an independently proved index for its excited-state residual separator. Ireland et al., [DOI 10.1021/acsphyschemau.1c00018](https://doi.org/10.1021/acsphyschemau.1c00018), explicitly use estimated excited lower bounds in their numerical examples. Ronto et al., [arXiv:2301.02827; DOI 10.1103/PhysRevA.107.012204](https://arxiv.org/abs/2301.02827), explain the auxiliary-root conditions and instances where naive lower-bound optimization fails. These are valuable **EMPIRICAL** calculations of paper formulas; the claimed digits were not adopted as certified inputs here.

Jennings' neutral H₂ lower-bound calculation, [DOI 10.1063/1.1841057](https://doi.org/10.1063/1.1841057), uses an intermediate operator and numerical five-dimensional quadrature without an interval remainder budget. Liu's recent [arXiv:2608.25760](https://arxiv.org/abs/2608.25760) reports a genuine interval pipeline for one-electron H₂⁺, with domain bracketing and exterior estimates; that implementation was not reproduced here. Its H₂⁺ result must not be relabelled as a helium or neutral H₂ enclosure. Thus the survey found useful mathematical lower-bound methods and high-precision helium calculations, but no audited source that already proves this uniform two-electron polynomial-bit theorem. This is a report of the sources inspected, not a claim that no other rigorous helium enclosure exists.

## 2. Route selection and exact uniform problem

**Chosen uniform route: (b), global H¹ approximation with a tracked rate.** Temple is preferable for a particular atom with a known separator, and that is what we execute in §3. For a uniform class, the H¹ route asks less of the trial approximation and matrix integration, and obtains the continuum lower bound directly. A promised relative gap by itself is not an absolute separator: a small residual might belong to an excited state.

There is a terminology correction to route (a). Temple requires (\phi\in D(H)=H^2\cap\mathcal H_f), so that (\|H\phi\|^2) exists. It does **not** require (\phi\in D(H\circ H)), nor fourth Sobolev derivatives. The notation (\langle H^2\rangle) is interpreted as the spectral second moment (\|H\phi\|^2). Ordinary continuous piecewise-linear H¹ elements need not satisfy the operator-domain requirement. The trial family below does.

Fix (Z_{\max}\in\mathbb N_{>0}), rational (0<r_{\min}<r_{\max}), and positive rational margins (\mu_{\rm gap},\mu_{\rm ion}). Inputs have two electrons, one or two fixed nuclei with integer charges between 1 and (Z_{\max}), and, for two nuclei, rational separation in ([r_{\min},r_{\max}]). Translation/rotation fixes the nuclei at 0 and (Re_1). Let (L) be the binary input length. The space and domains are

\[
\mathcal H_f=\bigwedge^2 L^2(\mathbb R^3\times\{\uparrow,\downarrow\};\mathbb C),\qquad
D(H)=H^2(\mathbb R^6;\mathbb C^4)\cap\mathcal H_f,\qquad
D(q)=H^1\cap\mathcal H_f.
\]

The Hamiltonian is exactly the Coulomb operator in the question, over all of configuration space. Sliced Hardy bounds make each Coulomb multiplier infinitesimally Laplacian-bounded; Kato–Rellich gives the self-adjoint realization on the displayed domain. The promised ground eigenvalue (E) is simple, its distance to every other spectral value is at least (\mu_{\rm gap}), and its distance to the essential spectrum is at least (\mu_{\rm ion}). These are mathematical promises, not an efficient membership test. Fixed nuclear positions do not assert equilibrium or stability against nuclear motion.

The constants in the elementary form estimates can be explicit. Put

\[
\bar Z=2Z_{\max},\quad B=\bar Z^2,\quad K=2\bar Z+1,\quad C=8\bar Z^2+1.
\]

**PROVEN (paper).** ( -B\le E\le0), (|q[f]|\le K\|f\|_{H^1}^2), and

\[
q[f]+C\|f\|_2^2\ge\|f\|_2^2+\tfrac14\|\nabla f\|_2^2. \tag{1}
\]

For the last inequality, Hardy bounds the attraction by (2\sqrt2\bar Z\|f\|_2\|\nabla f\|_2\le\tfrac14\|\nabla f\|_2^2+8\bar Z^2\|f\|_2^2); discard the nonnegative repulsion. The sharper lower-energy bound is the previously proved hydrogenic convex-combination bound (E\ge-N(\sum_A Z_A)^2/2). None of these constants establishes an exponential approximation rate.

### The single OPEN lemma

**CONJECTURED — uniform stable correlated-Gaussian approximation.** There exist explicit integers (a,d\ge1) and an explicit deterministic algorithm (D), depending only on the fixed class constants, as follows. Given the nuclear input (x) and integer (p\ge1), it outputs (m) antisymmetrized, normalized-primitive correlated Gaussian spin functions (\phi_j) and an integer (h). With (Q=a(L+p+1)^d),

\[
1\le m\le Q,\quad L+1\le h\le Q,\quad \operatorname{time}(D)\le Q^2,
\]

all rational parameters have bit height at most (h), exponent eigenvalues lie in ([2^{-h},2^h]), and some real coefficients satisfy

\[
\sum_j|c_j|^2\le2^h,\qquad
\left\|\sum_jc_j\phi_j-\psi\right\|_{H^1}\le2^{-p}. \tag{2}
\]

The primitives are (g_{A,s}(x)=[\det(2A)]^{3/4}\pi^{-3/2}\exp[-\sum_{d=1}^3(x^d-s^d)^TA(x^d-s^d)]), with rational positive-definite (2\times2) matrices (A), rational centers (s\in\mathbb R^6), and standard spin vectors before antisymmetrization. The algorithm receives no ground-state or energy oracle. It must construct a polynomial-size dictionary; enumerating all rational Gaussians does not qualify. No Gram condition number is assumed. This lemma combines approximation rate with coefficient stability, which are two aspects of the required effective approximation property. It is not a theorem supplied by the cited regularity papers.

### Full conditional proof skeleton and tracked cost

The [complete skeleton](helium_research/theorem_skeleton.md) contains the integral formulas, derivations, enclosure algorithm, bit representations, and proofs. The status of each dependency is explicit:

1. **PROVEN (paper):** continuum realization, form bounds (1), real choice of a simple ground state, and H¹ density of the allowed dictionary. Density supplies no rate.
2. **OPEN:** exactly (2), including explicit (D,a,d). This is the one substantive analytic research lemma.
3. **PROVEN (paper):** Gaussian Gram, kinetic, and Coulomb formulas by completing squares. **PROVABLE (implementation sketch):** evaluating their algebraic factors, exponentials, and Boys function by rational intervals costs at most (c_{\rm elem}(h+s+1)^8) for (s) bits. The algorithm and remainder choices are described; a numerical instruction-count constant has not been extracted from code.
4. **PROVEN (paper; scalar core also Lean):** if (\Phi c=\sum c_j\phi_j), (G=\Phi^*\Phi), (A_{ij}=q(\phi_i,\phi_j)), and (\tau=2^{-h-2p}), then (T=A+CG+\tau I\ge G+\tau I). Let (\lambda=\max_{c\ne0}c^TGc/(c^TTc)), and (E_{\rm reg}=1/\lambda-C). The weak eigenvalue equation cancels cross terms in (e=\Phi c_*-\psi), giving
   \[
   0\le E_{\rm reg}-E\le D_p:=4(K+B+1)2^{-2p}. \tag{3}
   \]
   In detail, (q[\Phi c_*]-E\|\Phi c_*\|^2=q[e]-E\|e\|^2\le(K+B)2^{-2p}); the penalty adds at most (2^{-2p}), while the norm squared is at least (1/4). Singular Gram matrices cause no difficulty because (T\ge\tau I).
5. **PROVEN (paper):** rounding both matrices to a common dyadic grid, perturbing the quotient by at most (\theta), and rational PSD bisection enclose (\lambda) between (l,v>0). With
   \[
   \epsilon=\min(2^{-b},\mu_{\rm gap}2^{-2b-1}),\quad D_p\le\epsilon/4,\quad
   \theta=\epsilon/[64(C+1)^2],
   \]
   the returned rational interval is
   \[
   [\ell,U]=[1/v-C-D_p,\ 1/l-C],\qquad U-\ell\le7\epsilon/16. \tag{4}
   \]
   A retained rational negative witness from the PSD tests supplies an explicit trial state with energy below (U). The spectral gap gives phase-adjusted L² state error at most (2^{-b}). Bounded observables require a specified computable matrix-element interface; arbitrary unspecified or unbounded observables are not included.
6. **PROVABLE (implementation sketch):** exact PSD tests and witnesses by fraction-free elimination, with a shared input denominator, cost at most (c_{\rm psd}m^5(B_{\rm entry}+\lceil\log_2(m+1)\rceil+1)^2). The common denominator and determinant bounds are exhibited. Output formatting has a fixed constant (c_{\rm out}). These routine implementation obligations are not claimed completed or Lean formalized.

For traceability, let (H_\mu) be the binary length of fixed (\mu_{\rm gap}), and set

\[
\begin{aligned}
c_\mu&=H_\mu+\max(0,\lceil\log_2(2/\mu_{\rm gap})\rceil),\\
c_p&=2+c_\mu+\lceil\log_2(16(K+B+1))\rceil,\\
c_C&=\lceil\log_2(C+2)\rceil,\\
S_0&=c_\mu+3c_C+16,\qquad B_0=4S_0+16c_C+32,\\
J_0&=c_\mu+2c_C+10,\\
C_0&=1+16c_{\rm elem}(S_0+2)^8+c_{\rm psd}J_0(B_0+3)^2+c_{\rm out}.
\end{aligned}
\]

The required resolution obeys (p\le b+c_p); assembly and finite algebra cost at most (C_0Q^{10}). Therefore the **conditional** bound is

\[
\operatorname{cost}\le C_{\rm total}(L+b+1)^P,\quad
P=10d,\quad C_{\rm total}=C_0a^{10}(1+c_p)^{10d}. \tag{5}
\]

These formulas expose, rather than hide, the missing constants. No numerical (a,d,D) or implementation instruction constants have been established. Thus (5) is not an unconditional (C(L+k)^p) theorem. Geometry and ionization enter through the OPEN lemma; the spectral gap also enters the displayed elementary constants. The literature supports exponential approximation under relevant types of regularity, but a new proof tracking those constants through collisions, infinity, dictionary construction, and coefficient stability is still needed.

## 3. Executed helium certificate

**PROVEN (paper proof only, with an exact arithmetic computation outside Lean).** This section concerns the original unrestricted helium operator, not just the bottom of a finite matrix. It uses route (a) as an independent posterior certificate. It is not an execution of the unproved uniform algorithm (2)–(5).

### Analytic spectral separator

The charge-two one-electron operator (h=-\Delta/2-2/r) has a rank-two spin ground subspace at (-2), and the remaining spectrum is at least (-1/2). On the two-electron fermionic space, the noninteracting (h_1+h_2) therefore has a unique (1s^2) determinant at (-4), and its orthogonal complement has energy at least (-5/2). Let (P_0) be the rank-one determinant projection. Positive electron repulsion gives

\[
H\ge-4P_0-\tfrac52(I-P_0). \tag{6}
\]

If the spectral projection of (H) below (-5/2) had dimension at least two, its range would contain a nonzero vector orthogonal to (P_0); (6) would contradict that vector's strictly smaller spectral expectation. Thus its rank is at most one. The (1s^2) determinant has exact expectation (-4+5Z/8=-11/4<-5/2), so the projection is nonzero. A rank-one reducing spectral subspace is an eigenspace. Consequently

\[
\sigma(H)\subset\{E_2\}\cup[-5/2,\infty),\qquad \beta=-5/2. \tag{7}
\]

This proves existence and simplicity of the actual full-spin ground state below the separator. It does not guess an excited energy or rely on singlet-sector ordering. The full argument, including the elementary repulsion integral, is in [lower_bounds.md](helium_research/lower_bounds.md).

### Temple proof and exact trial

For a normalized (\phi\in D(H)), put (m=\langle\phi,H\phi\rangle<\beta) and (v=\|H\phi\|^2-m^2). The spectral measure is supported where ((\lambda-E_2)(\lambda-\beta)\ge0). Its second moment is finite, and integration gives

\[
0\le v+(m-E_2)(m-\beta),\qquad
m-\frac{v}{\beta-m}\le E_2\le m. \tag{8}
\]

The trial is the spin singlet times the symmetric Hylleraas function

\[
\Phi=e^{-2(r+s)}\sum_{i\ge j\ge0,\ k\ge0,\ i+j+k\le\Omega}c_{ijk}P_{ijk},
\]

where (r=|x_1|,s=|x_2|,u=|x_1-x_2|). For (i>j), (P_{ijk}=(r^is^j+r^js^i)u^k/(i+j+k)!); for (i=j) the duplicate term is omitted. Every coefficient is a rational number explicitly supplied in the trial JSON. The finite trial lies in H²: first distance derivatives are bounded; second derivatives contribute at most one inverse distance, square-integrable in its three normal dimensions; exponential decay controls infinity. Integration by parts across shrinking collision tubes introduces no surface delta. This argument concerns the original nonnegative-power trial, not an arbitrary Laurent ansatz.

The checker differentiates the trial in the full continuum and computes (S=\|\Phi\|^2), (H_1=\langle\Phi,H\Phi\rangle), and (H_2=\|H\Phi\|^2). In particular it does **not** square the projected finite Hamiltonian. After cancelling the common (8\pi^2) angular factor, (S,H_1\in\mathbb Q), while (H_2\in\mathbb Q+\mathbb Q\log2+\mathbb Q\pi^2). The action and complete moment derivations are in [THEORY.md](helium/THEORY.md) and [helium_method.md](helium_research/helium_method.md).

Only rational interval operations enter (8). For example,

\[
\log2=2\sum_{n=0}^{K-1}\frac1{(2n+1)3^{2n+1}}+R_K,
\qquad 0<R_K\le\frac9{4(2K+1)3^{2K+1}}.
\]

Machin-series rational bounds enclose (\pi). The variance upper endpoint is substituted in (8), and decimal endpoints are rounded outward by exact integer division. Trial selection uses high-precision Decimal arithmetic and a rational energy target, but neither its eigenvalue estimate nor the published reference is trusted by the certificate. Changing the optimizer or target cannot invalidate a successfully recomputed certificate.

### Numerical certificate and comparison

The order-20 trial has **946 rational coefficients**, with exponent exactly 2. The executed certificate is

\[
\boxed{
\ell=-\frac{1451862601431}{500000000000}
=-2.903725202862
\ \le E_2\le\
u=-\frac{362965546259}{125000000000}
=-2.903724370072 .}
\]

Its exact width is

\[
\boxed{u-\ell=\frac{83279}{100000000000}
=0.000000832790<\frac1{1000000}\ \text{hartree}.}
\]

The [full trial](helium/trial_residual_20.json) specifies every coefficient and basis index. The [512-bit certificate](helium/certificate_residual_20_512.json) and [768-bit certificate](helium/certificate_residual_20_768.json) record exact rational moments, the coefficients of (1,\log2,\pi^2), directed variance bounds, and the Temple division. Both verifications passed using rational outward arithmetic, with identical final endpoints and exact moments; the 768-bit variance interval lies inside the 512-bit one. The fresh [512-bit log](helium/residual_20_check512.log) and [768-bit log](helium/residual_20_check768.log) record approximately 115 seconds per verification on this machine. Display-only summaries of the exact certificate values are

\[
m\approx-2.9037243700726468286055973905,\quad
v\approx3.3621709309782374841\times10^{-7},\quad
\beta-m\approx0.4037243700726468286.
\]

No finite-basis convergence assertion is required to validate this interval. For context, the preceding 372-term trial certified width (5.022108\times10^{-6}); increasing interval precision could not repair that width because the trial's residual, not rounding, dominated it. Optimizing the residual and increasing the polynomial order supplied the improvement. These two finite results do not prove an asymptotic convergence rate.

This certificate also places helium inside a nonempty instance of the proposed class: (7) and the upper endpoint imply a gap above the ground greater than (2/5) hartree. The HVZ threshold is the one-electron energy (-2), so its ionization margin exceeds (9/10) hartree. The spectral/domain/HVZ assertions in these deductions are paper mathematics.

The reference used only for comparison is Schwartz's extrapolated infinite-mass value

\[
E_{\rm ref}=-2.9037243770341195983111592451944044466969253105,
\]

from [math-ph/0605018, p.3](https://arxiv.org/abs/math-ph/0605018). It is the most precise infinite-mass benchmark verified in this targeted survey; the recent SWEXPHC paper, [DOI 10.1016/j.cpc.2025.109920](https://doi.org/10.1016/j.cpc.2025.109920), also discusses the 46-significant-figure helium benchmark. This is **EMPIRICAL** numerical precision, not an independently interval-certified exact energy or a verified priority claim. No digit from the reference is an input to the lower-bound proof.

The exact trial mean minus that finite reference string is approximately (6.96147276970556\times10^{-9}) hartree. The outward upper endpoint is (6.96211959831116\times10^{-9}) above it; the lower endpoint is (8.25827880401689\times10^{-7}) below it. The reference therefore lies inside the interval. There is no discrepancy above 1 mHa; the entire interval is only (0.000832790) mHa wide. The certificate stores the differences as rational numbers. Finite nuclear mass, relativistic, and QED values concern different Hamiltonians and are not compared to this result.

### Reproduction and independent checks

The complete code and input files are linked with the final result. Python's standard library suffices. Verification reads only the rational trial, recomputes its full moments, and writes a certificate; it does not rerun the older Gaussian reduction or require trial optimization. The checker rejects JSON floating-point parameters and records the SHA-256 of the trial. All load-bearing output numbers are rational strings, integers, or booleans; timings are log-only.

An [independent exact audit](helium/independent_audit.md) checks the moment formulas using separate positive perimetric and Laplace-integral recurrences, checks the Hamiltonian action by Cartesian automatic differentiation, and checks kinetic forms independently. Its [script](helium/independent_audit.py) and [log](helium/independent_audit.log) record the counts and source hashes. These checks strengthen the computer-assisted paper proof; they do not turn the continuum identities or Python execution into Lean theorems.

## 4. Machine-checked result and exact trust boundary

**PROVEN (Lean).** [Temple.lean](formal/Temple.lean) proves Temple's inequality for an actual nonzero finite-dimensional complex Hermitian linear operator. It defines the Rayleigh mean and residual from that operator, derives their spectral-moment identities using Mathlib's orthonormal eigenbasis, identifies the smallest eigenvalue as the least member of the actual operator spectrum, and proves

\[
m-\|T\phi-m\phi\|^2/(\beta-m)\le\min\sigma(T)\le m.
\]

Its separator is an explicit hypothesis about every distinct spectral value above the ground value. Ground-state degeneracy is allowed. This is not merely a scalar inequality with the spectral identities assumed. It also proves an outward interval version.

[TempleScalars.lean](formal/TempleScalars.lean) proves the finite weighted Temple argument, interval propagation, coarse-gap bootstrap, residual tolerance, normalization lower bound, regularized energy quotient estimate, and reciprocal perturbation estimate. It extends the existing project without asserting any continuum assumptions as axioms. There are **22 new public theorems**, and **76 public theorems** in the four scientific modules as built. A private helper is also kernel-checked and included transitively in the axiom audit.

Every new top-level theorem has a plain-English paragraph and a preceding human proof in [TEMPLE_STATEMENTS.md](formal/TEMPLE_STATEMENTS.md) and [TEMPLE_SCALAR_STATEMENTS.md](formal/TEMPLE_SCALAR_STATEMENTS.md). These explain which operator quantities are defined, which facts are proved, and which separator/approximation assumptions remain inputs.

Exact versions: **Lean 4.34.0-rc2**, compiler commit `6a10ac8c22beadecabdbb0919c2b50214762f91d`; **Mathlib** `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`. The project remains pinned for reproduction; this report does not claim an unverified moving latest revision.

The [aggregate build log](formal/helium-logs/lake-build.log) ends `Build completed successfully (8914 jobs).` The [status record](formal/helium-logs/build-status.json) records exit code 0 for the build, axiom audit, and source audit. All 76 public declarations have transitive axiom sets containing only `propext`, `Classical.choice`, and `Quot.sound`; there is zero `sorry`, zero added `axiom`, and no `native_decide`. See [axiom-audit.log](formal/helium-logs/axiom-audit.log) and [verification instructions](formal/helium-logs/README.md).

**Not Lean-checked:** the unbounded Coulomb operator, its hydrogenic comparison and HVZ threshold, the trial's Sobolev membership, the continuum integral formulas, the Python interval execution, and the uniform algorithm or its runtime. The latter remains a conditional skeleton. The finite-dimensional Temple theorem must not be substituted for the infinite-dimensional spectral-measure proof without this distinction.

## 5. Where a hand-wave would have changed the result

- **A nearby eigenvalue versus the ground state:** proved the full fermionic separator (-5/2) analytically; did not use an excited Ritz value or a guessed residual index.
- **The square of a projection versus the second continuum moment:** evaluated (H\Phi) before integration, retaining its components outside the trial space.
- **H¹ versus operator domain:** proved H² membership for the particular polynomial-distance trials; did not claim generic H¹ elements have a strong residual.
- **All-order regularity versus an effective exponential rate:** kept the latter as the one OPEN lemma, including construction and coefficient bits. Intersecting collisions and infinity are not discarded.
- **Exponential hp error versus polynomial bit complexity:** recorded the actual spatial dimension and regularity assumptions, and separated integration/linear algebra implementation constants from the analytic rate.
- **A small Gram eigenvalue:** used an explicit coefficient regularizer and proved its approximation error; did not assume an unverified condition number.
- **High precision versus certification:** Decimal arithmetic only selects a candidate. Rational recomputation, explicit transcendental remainders, and outward rounding determine the interval.
- **A paper reporting guaranteed digits:** recorded separator/index and rounding limitations, rather than adopting its numerical table as a certified input.
- **Unread originals:** marked Kato, Klahn–Bingel, Hill, and original Lehmann/Maehly access limits; did not substitute a citation for having checked the hypotheses.
- **A schematic cost constant:** gave its dependency formula and labelled the missing implementation constants. No unconditional runtime theorem is claimed.

## 6. Honest scope and three electrons

This work yields a concrete continuum certificate for one two-electron atom, an actual finite-dimensional Lean Temple theorem, and a conditional uniform two-electron algorithm with a precise remaining analytic target. It neither solves general many-electron Coulomb systems nor proves an exact characterization of all tractable classes. A width certificate for helium does not prove polynomial convergence as the requested number of bits increases.

There is an immediate correction needed before extending the class to three electrons. For an odd number of electrons without magnetic or spin-dependent terms, a simple eigenvalue on the **full spin space** cannot occur. Indeed the Hamiltonian commutes with (S_z); a one-dimensional eigenspace would have a fixed nonzero half-integer (S_z). Global spin flip gives an orthogonal vector at the same energy and opposite (S_z), a contradiction. Thus the original simple-ground predicate is empty for three electrons. A meaningful extension must instead promise an isolated ground multiplet, or work in a specified spin sector with appropriate uniqueness assumptions. State and observable guarantees must then be phrased for that sector or ground subspace.

Temple itself permits an isolated degenerate ground energy, as the Lean theorem does. The obstacle is constructing its separator and trial. The rank-one (1s^2) comparison that makes helium easy does not isolate lithium's (1s^2 2\ell) shell; hydrogenic degeneracies and electron repulsion require a different lower comparison. The six-dimensional Hylleraas moment reduction also does not automatically generalize to nine-dimensional three-electron integrals. Fixed-three-electron Gaussian form integrals remain tractable in principle, but effective approximation across more collision strata needs a new proof. It is plausible that the H¹ route extends for fixed particle number with a larger exponent; no such theorem or uniform-in-(N) polynomial bound is proved here.

**The precise next theorem to prove or refute is the uniform stable correlated-Gaussian approximation lemma (2), with an explicit dictionary generator and explicit (a,d), for the stated gapped, ionization-separated two-electron class.** Proving it and completing the labelled elementary implementations would establish the restricted polynomial-bit result (5). Refuting it would invalidate this particular approximation route, not every possible algorithm for that physical class.
