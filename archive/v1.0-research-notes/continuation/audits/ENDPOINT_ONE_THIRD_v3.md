> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Endpoint one-third by degree-dependent finite-order cutoffs, version 3

Date: 2026-09-09. Evidence: **conditional paper theorem; no Lean verification and no physical numerical certificate.**

Under the explicit physical regularity and tail assumptions G1–G3 stated below, the unchanged two-electron dictionary admits the endpoint estimate

\[
\forall n\ge0\quad\exists v_n\in V_n^{(Z)}:
\qquad \|\psi-v_n\|_{H^2_*}\le C e^{-c n^{1/3}}.
\tag{E0}
\]

This is a separate new construction. It replaces the fixed Gevrey cutoffs by degree-dependent cutoffs with controlled derivatives only up to a selected finite order. It is **not** a limit in the cutoff parameter of `ANALYTIC_TARGETED_v2.md`; the constants in that earlier theorem remain uncontrolled in such a limit. That sealed earlier file is unchanged.

The new core result is a self-contained polynomial lemma giving a C² error bounded by CMh^(−2)(q+1)^7 exp(−bhq), while controlling the **same** polynomial throughout the cone, including outside its fitting shell. The low-hq factor h^(−2) is necessary for the proof's small-degree fallback and is explicitly retained. No general multivariate approximation theorem is assumed.

## 1. Exact physical assumptions and unchanged target

Electron count is N=2, approximation order is n, and requested computational precision p is unused. The auxiliary polynomial degree is q, Poisson order is k, cutoff differentiability order is m, and B=m+2 counts one-dimensional convolution kernels.

Fix Z≥2. In actual physical variables (x₁,x₂)∈R⁶, let r=|x₁|, s=|x₂|, u=|x₁−x₂|, S=r+s. In half-perimetric variables (a,b,c)≥0, r=b+c, s=a+c, u=a+b and S=a+b+2c. Assume ψ is a real, exchange-symmetric, rotation-invariant physical function with ||ψ||₂=1, continuous at zero. Set ψ₀=ψ(0) and f=ψ̂−ψ₀. Assume:

* **G1.** For fixed Cᵥ,Aᵥ,δᵥ>0 and 0<σ<1, every reduced multi-index satisfies |∂^ν f|≤CᵥAᵥ^|ν||ν|!S^(σ−|ν|) on 0<S<δᵥ, with compatible analytic germs at every nonvertex boundary point.
* **G2.** For one fixed 0<d<δᵥ/8, every closed-octant point with S≥d has compatible holomorphic perimetric polydiscs of radius c_d/(1+S), bounded by M_d, for fixed c_d,M_d>0. Germs agree on their common continuations of the actual reduced function.
* **G3.** ψ∈H²(R⁶), and ||ψ||_{H²_*(S>R)}≤C_t exp(−γR) for R≥1 and fixed C_t,γ>0. The norm counts the physical L² norm, gradient norm, and full Frobenius Hessian norm.

The dictionary remains exactly

\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
e^{-Z2^jS}\mathcal P_{n-2j}^{\rm sym}(r,s,u).
\tag{E1}
\]

The perimetric and distance variables are linearly related, so they give the same polynomial degree spaces. Symmetry is a↔b, equivalently r↔s. Tensoring with the unit spin singlet places the spatial witness in the full fermionic spin-space under simultaneous spatial and spin exchange, preserving norms.

These hypotheses are explicit unresolved physical inputs here. The conditional theorem does not establish G1, G2, G3, a self-adjoint Hamiltonian, its spectrum, its ground state, or an algorithm for computing ψ-dependent coefficients.

## 2. An explicit finite-order cutoff

For m≥1 put B=m+2, and define the probability density

\[
\eta_B(t)=B\,\mathbf1_{[-1/(2B),\,1/(2B)]}(t),
\qquad
\rho_m=\mathbf1_{[-3/2,\,3/2]}*\eta_B^{*B}.
\tag{E2}
\]

Convolution with a nonnegative probability density preserves values in [0,1]. The total support radius of the B kernels is 1/2. Consequently ρ_m is supported in [−2,2] and equals one on [−1,1].

The distributional derivative of each kernel is the signed measure

\[
\eta_B'=B(\delta_{-1/(2B)}-\delta_{1/(2B)}),
\qquad\|\eta_B'\|_{\rm TV}=2B.
\]

For any 0≤r≤m, differentiate r distinct kernels in the convolution. There is no binomial coefficient: convolution differentiation can be assigned to any one factor at each step. It follows that

\[
\|\rho_m^{(r)}\|_\infty\le(2B)^r\le(6m)^r.
\tag{E3}
\]

At least B−r≥2 undifferentiated kernels remain. Their convolution with the bounded interval indicator is continuous; convolution with the finite signed derivative measures preserves continuity. Thus the displayed weak derivatives have continuous representatives through order m, and ρ_m∈C^m(R). All its derivatives through order m vanish at ±2 because it is C^m and identically zero beyond its support. The stated endpoint values and derivative bounds therefore hold globally, including the support boundary. Only this finite differentiability is needed.

This construction uses the familiar finite-order localization principle associated with Ehrenpreis cutoffs. A primary research paper, Strohmaier–Witten, *Analytic States in Quantum Field Theory on Curved Spacetimes* (2024), [Appendix B.2](https://link.springer.com/article/10.1007/s00023-024-01419-0), records derivative-controlled cutoff sequences in its discussion of analytic wavefront sets. The paper's quantum-field conclusions are not used, and its cutoff assertion is not a premise: equations (E2)–(E3) prove the precise finite-order statement needed here. No novelty of the cutoff device is claimed.

For an exact finite representation of this auxiliary cutoff, iterating the interval integrations in (E2) gives

\[
\rho_m(t)=\frac{B^B}{B!}\sum_{j=0}^B(-1)^j\binom Bj
\left[(t+2-j/B)_+^B-(t-1-j/B)_+^B\right].
\tag{E2a}
\]

Each convolution by η_B is B times the difference of two shifted primitives; expanding the B differences proves this formula. The knots and polynomial coefficients are rational. The supporting finite-instance checker converts its derivative polynomials on each transition subinterval to Bernstein form; the convex-hull bound for the Bernstein basis proves the reported interval enclosures on whole subintervals. This is a certificate path for auxiliary cutoff polynomials, not for an energy or wavefunction.

## 3. Uniform finite-order extension from local holomorphic charts

Let

\[
K=\{y\ge0:1/4\le S(y)\le2\}.
\]

Suppose F is real on K and has compatible holomorphic polydiscs of common radius 0<h≤1/100 at every point of K, each bounded by M. These germs are real on their real neighborhoods by uniqueness from the real interior of K. For each m≥1 there exists G_m∈C_c^m((−4,4)³), equal to F on a real neighborhood of K, with

\[
\|G_m\|_\infty\le M,\qquad
\|\partial^\nu G_m\|_\infty
\le125M(12096m/h)^{|\nu|}\quad(1\le|\nu|\le m).
\tag{E4}
\]

Here is the construction and constant accounting. Use lattice spacing ℓ=h/16, retaining centers c_j∈ℓZ³ whose closed half-cells of radius ℓ/2 meet K, and choose x_j in that intersection. Let

\[
\chi_j(y)=\prod_{i=1}^3\rho_m((y_i-c_{j,i})/\ell),\qquad
\beta_j=\chi_j\prod_{i<j}(1-\chi_i).
\]

The support of χ_j is contained in the cube of radius 2ℓ about c_j, hence lies within radius (5/2)ℓ<h/4 about x_j. The corresponding analytic chart F_j retains at least an h/2 Cauchy radius on this support. The cutoffs equal one on radius-ℓ cubes about the centers, so at least one equals one throughout an ℓ/2-neighborhood of K. Set G_m=Σ_jβ_jF_j, each summand extended by zero off its chart. This is C^m because the support lies strictly inside the chart and the cutoff jets vanish on its support boundary.

At every point at most 5³=125 lattice supports are active. Every inactive cutoff has zero jets through order m. Thus at a point each nonzero product jet involves at most 125 cutoff factors, irrespective of the total number of charts, and at most 125 summands contribute. The telescoping weights are nonnegative and sum to at most one, proving the zero-order bound. Where their sum equals one, compatibility gives G_m=F.

By (E3), each cutoff derivative of order r≤m is bounded by (96m/h)^r. On its support the analytic factor has bound M(2/h)^r r!≤M(2m/h)^r. Leibniz for at most 126 factors has multinomial sum at most 126^r, so its r-th derivative is bounded by M(126·96m/h)^r. Summing at most 125 terms gives (E4). This is the point where bounded overlap prevents a factor depending on h^(−3) in the derivative base.

## 4. Cosine composition without an extra factorial

Put g_m(θ)=G_m(4cosθ₁,4cosθ₂,4cosθ₃). It is C^m, periodic and even in each variable. For r≤m, its derivative in one angular variable is bounded by

\[
\|\partial_{\theta_i}^r g_m\|_\infty
\le125M(50000m/h)^r.
\tag{E5}
\]

To prove this, the Faà di Bruno formula with all derivatives of 4cos bounded by 4 gives an upper bound 125MΣ_{j=1}^r S(r,j)A^j, where A=4·12096m/h and S(r,j) is a Stirling number of the second kind. The elementary combinatorial bound

\[
S(r,j)\le\binom rj j^{r-j}\le\binom rj r^{r-j}
\]

follows by choosing a designated representative in each block and assigning the remaining elements to those representatives; using the least element in each block gives an injection from set partitions into these assignments. Hence

\[
\sum_jS(r,j)A^j\le(A+r)^r\le(48385m/h)^r
\le(50000m/h)^r.
\]

The coefficient bound uses r≤m and h≤1. This avoids the erroneous extra r! that would result from a coarser composition estimate and would destroy the endpoint balance.

## 5. C² polynomial approximation and the same polynomial outside K

There are universal C,b>0 such that for all q≥0 and 0<h≤1/100 as above, there is a real polynomial Q_q of total degree at most q with

\[
\max_{|\nu|\le2}\sup_K|\partial^\nu(F-Q_q)|
\le CMh^{-2}(q+1)^7e^{-bhq}.
\tag{E6}
\]

For this **same polynomial**, on the nonnegative cone with t=S(y),

\[
\begin{array}{ll}
|\partial^\nu Q_q(y)|\le CM(q+1)^7,&0\le t\le2,\\
|\partial^\nu Q_q(y)|\le CM(q+1)^7(6t)^q,&t\ge2,
\end{array}
\quad |\nu|\le2.
\tag{E7}
\]

One may symmetrize under a↔b whenever F is symmetric. We give all degree and small-parameter details.

Let C₀=50000. In the regime hq≥192C₀, set D=⌊q/3⌋ and

\[
m=\left\lfloor\frac{hD}{4C_0}\right\rfloor.
\tag{E8}
\]

Then D≥q/6≥1, hD≥32C₀, m≥8, and m≥hD/(8C₀). Use precisely G_m and g_m from §§3–4. Integration by parts m times in a largest-frequency direction shows that a Fourier coefficient of maximum frequency R>0 is bounded by

\[
125M\left(\frac{C_0m}{hR}\right)^m.
\]

Evenness gives a tensor Chebyshev expansion in the algebraic coordinates, with the usual grouping of at most eight Fourier coefficients. Each Chebyshev coefficient is therefore bounded both by 8M and by 1000M(C₀m/(hR))^m. Let Q_q be its truncation to degree D in each variable. Its total degree is at most 3D≤q.

For the C² tail, there are at most 3(R+1)² nonnegative frequency triples of maximum R. Derivatives of total order at most two of the tensor Chebyshev polynomial on [−4,4]³ cost at most C(R+1)^4. Since C₀m/h≤D/4, the tail is at most a fixed constant times

\[
M\sum_{R>D}(R+1)^6\left(\frac D{4R}\right)^m
\le64M4^{-m}D^m\int_D^\infty x^{6-m}\,dx
=\frac{64M D^7 4^{-m}}{m-7}.
\tag{E9}
\]

The frequency-count and coefficient constants are absorbed into C. Absolute convergence through two algebraic derivatives follows from m≥8. Fourier uniqueness identifies the original g_m with its series; the coordinatewise cosine map covers the cube. Uniform convergence of the series and its first two polynomial derivatives then identifies its C² sum with G_m, including on cube boundaries. On the neighborhood of K this is F.

Because m≥hD/(8C₀) and D≥q/6, (E9) is bounded by CM(q+1)^7exp(−bhq), with

\[
b=\frac{\log4}{48C_0}>0.
\tag{E10}
\]

This even proves (E6) without h^(−2) in the high-hq regime. In the complementary regime hq<192C₀ choose Q_q=0. Cauchy's inequalities directly give a C² norm bound 2Mh^(−2) on K, while exp(−bhq)≥exp(−4log4)=1/256. Enlarging C to at least 512 proves (E6) uniformly. Omitting h^(−2) in this low-hq argument would be invalid.

For (E7), in the nonzero case there are (D+1)³≤(q+1)³ coefficients, each bounded by 8M because ||g_m||∞≤M. Two coordinate derivatives on the cube cost at most (q+1)^4. Thus the polynomial's cube C² norm is at most CM(q+1)^7. Outside the cube use the elementary Chebyshev estimate

\[
|T_j^{(i)}(x/4)|4^{-i}
\le C(j+1)^{2i}(1+|x|/2)^j\quad(i\le2).
\]

Each nonnegative coordinate is at most t and 1+t/2≤t for t≥2. Total degree at most q and the same coefficient count then give the second line of (E7), with the conservative base 6t retained from the inherited proof. The zero-polynomial fallback satisfies (E7) automatically. Symmetrization preserves every set, bound and degree used here.

The construction depends on q; there is no assertion that the G_m converge to a compactly supported analytic extension. A single nonzero compactly supported analytic cutoff would be impossible, but none is used.

## 6. Rescaled shells and global physical estimate

Under G1–G2, for every T≥1 and 0<τ≤T, F_τ(y)=τ^(−σ)f(τy) has compatible bounded holomorphic charts on K with

\[
h_T=c_h(1+T)^{-2},\qquad M=M_h,
\tag{E11}
\]

where c_h,M_h are independent of T,τ and c_h is reduced to make h_T≤1/100. This is the parameter-dependent G6 consequence: the scaled vertex factorial estimates give a uniform local radius for small τ, while the exterior radius rescales to at least c/[τ(1+2τ)] and the amplitude τ^(−σ) is bounded on scales bounded below. Both ranges include compatibility as a hypothesis.

From (E6)–(E7) we obtain symmetric degree-q shell polynomials with fitting error

\[
C(q+1)^7(1+T)^4
\exp\left[-\frac{b' q}{(1+T)^2}\right].
\tag{E12}
\]

Their cube/exterior bounds can use the same prefactor M_{T,q}=C(q+1)^7(1+T)^4; to match the old tail calculation we may further enlarge the exterior bound by (q+1)^4. The prefactor also dominates the global finite-order envelope (1+S)^4 on lower shell tails.

Retain k=J=256(q+1), a_j=Z2^j, τ_j=k/a_j, and j₀ the least index with a_{j₀}≥k/T. Require the eventual conditions

\[
k/T>Z,\quad2^J\ge2k/(ZT),\quad T\ge16,\quad
\tau_*:=k/(Z2^{J+1})\le1,\quad2\tau_*<\delta_v.
\tag{E13}
\]

Then j₀≤J and T/2<τ_{j₀}≤T. Let

\[
E_k(t)=e^{-t}\sum_{l=0}^k t^l/l!,\quad
P_j=\tau_j^\sigma Q_{\tau_j,q}(\cdot/\tau_j),
\]

\[
v_q=\psi_0E_k(a_{j_0}S)
+\sum_{j=j_0}^J[E_k(a_jS)-E_k(a_{j+1}S)]P_j.
\tag{E14}
\]

The exact dictionary index is k+q+2(J+1)=769q+770. Each term is a distance polynomial times an allowed exponential, in physical H²; the inverse-distance Hessians are square-integrable in their three transverse coordinates. Auxiliary cutoffs are absent from this final vector.

The exact telescoping error identity is

\[
\psi-v_q=\psi[1-E_k(a_{j_0}S)]+fE_k(a_{J+1}S)
+\sum_{j=j_0}^J[E_k(a_jS)-E_k(a_{j+1}S)](f-P_j).
\]

The fit/lower-tail/upper-tail/inner/outer calculations in frozen G15–G23 now apply to the new polynomials:

* Fitted physical shell norms contribute (k+1)³τ_j^(σ+1)(1+τ_j²) times (E12).
* Lower Poisson tails retain the vanishing power (4t)^(k/2), which absorbs inverse powers from derivatives at zero. The envelope (1+T)^4 is included in M_{T,q}.
* The actual polynomial upper tails retain (6t)^q. The squared integral remains bounded by a prefactor times 12^(2q)e^(−k/2)·2²²/(2k−2q−22), and hence is exponentially small for k=256(q+1).
* The geometric sum of physical shell scales is at most C(1+T)^4. Thus multiplying M_{T,q} contributes (q+1)^7(1+T)^8 overall.
* The inner omitted term is bounded by C(k+1)³τ_*^(σ+1). The outer omitted target is still the decaying physical ψ; its localized Hardy and H²-tail estimate is bounded by C(k+1)³[e^(−k/16)+e^(−γT/16)].

The physical C²-to-H² integral formula and removability argument are D11–D12 and lines 196–198 of the frozen local proof. They are finite-order facts independent of how the shell polynomials were constructed. These inherited paper derivations are reused with their explicit function/domain assumptions, not represented as Lean theorems.

Keeping the original extra factor (q+1)^4 in the tail estimate gives the safe global bound

\[
\begin{split}
\|\psi-v_q\|_{H^2_*}\le C(k+1)^3(q+1)^{11}(1+T)^8\bigg[
&e^{-b' q/(1+T)^2}+e^{-k/16}\\
&+e^{-\gamma T/16}
+\left(\frac{k}{Z2^{J+1}}\right)^{\sigma+1}\bigg].
\end{split}
\tag{E15}
\]

No tail of a compactly supported surrogate is substituted for the tail of the actual polynomial witness.

## 7. Endpoint balance, all n, and residual interpretation

Choose T=(q+1)^(1/3). The conditions (E13) hold for every q beyond a finite threshold: T and k/T grow, and 2^J dominates polynomial scales. The shell exponent satisfies

\[
\frac{b' q}{(1+T)^2}\ge\frac{b'}{4\,2^{2/3}}q^{1/3}.
\]

The physical tail contributes exp(−γq^(1/3)/16). The Poisson term is at most exp(−16q^(1/3)); the inner term is at most exp[−128(σ+1)(log2)q^(1/3)], using k≤2^(k/2), Z≥2 and J=k. Thus the bracket is at most 4exp(−ηq^(1/3)) for a fixed positive η.

The prefactor is at most

\[
257^3 2^8(q+1)^{50/3},
\]

because 3+11+8/3=50/3. With x=q^(1/3), q^(50/3)=x^50 and sup_{x≥0}x^50e^(−ηx/2)=(100/(eη))^50. Hence (E15) gives C′exp(−ηq^(1/3)/2).

For sufficiently large n use q=⌊(n−770)/769⌋. Then v_q∈V_n and q≥n/1538 for n≥3078. For finitely many smaller indices take zero and enlarge C using ψ∈H². This proves (E0) for every n.

If additionally ψ satisfies the actual continuum eigenvalue equation on the actual H² domain for H_Z=−(Δ₁+Δ₂)/2−Z/r−Z/s+1/u with eigenvalue E and |E|≤Z², the sliced Hardy graph estimate

\[
\|(H_Z-E)e\|_2\le(\sqrt6/2+4Z+2+Z^2)\|e\|_{H^2_*}
\]

transfers (E0) to unit dictionary vectors with residual Ce^(−cn^(1/3)). For large n divide v_n by its norm, which is at least 1/2; for finitely many small n use normalized e^(−ZS). The eigenfunction/domain premise remains visible. This argument does not identify E with the continuum spectral infimum.

This is an existence and approximation-rate theorem under exact function-space hypotheses. The procedure constructing cutoffs is explicit, but its polynomial coefficients depend on the unknown analytic charts of ψ. It therefore supplies neither a physical energy algorithm nor rational coefficients, certified output intervals, a termination theorem, or a bit-complexity result.

## 8. Provenance, review, and next frontier

Frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`; annotated tag `theorem-t-proof-freeze-2026-09-09`. All frozen paths below are relative to `THEOREM_T_FREEZE_2026-09-09_212604/`:

| Frozen source | SHA-256 | Used scope |
|---|---|---|
| `RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` | Target dictionary and physical verification boundary. |
| `rwa_proof/GLOBAL_DYADIC_ATTEMPT.md` | `b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b` | G1–G6 and conditional G15–G27 composition. |
| `rwa_proof/DYADIC_REMAINDER_ATTEMPT.md` | `bb30295c982758a93237b583a6d52d3490c49b0d8f0737036faa4e701d997b02` | Degree/Chebyshev growth, physical C² conversion, weak removability. |

These hashes matched the frozen manifest in the preceding targeted audit; the v3 provenance record rechecks them. The sealed prior targeted theorem has SHA-256 `d065961f0385cce69af537df32fffa08ab4872153fdb213d5b39fcf5d3969c2e`. This file is a stronger new argument, not an edit to its historical status. No false inherited claim is alleged.

The supporting script `endpoint_cutoff_checks_v3.py` constructs exact rational piecewise-polynomial cutoff instances and checks Bernstein coefficient enclosures, endpoint jets, and the combinatorial inequalities for selected orders. Those finite computations do not prove the all-order analytic theorem or certify physical energies. Their precise scope and hashes are recorded with the output.

The independent exact-argument review is `ENDPOINT_ONE_THIRD_INDEPENDENT_REVIEW_v1.md`. It retains the physical G1–G3 assumptions and the paper status of the inherited tail composition. The completed proof, review, checker, output and source-integrity checks are bound by `ENDPOINT_ONE_THIRD_PROVENANCE_v3.json`. Review agreement is supporting evidence, not a replacement for proof.

The next unresolved step for a physical theorem remains proving G1–G3 and the continuum operator/spectral hypotheses in the required foundation. The new endpoint approximation lemma itself is a suitable independent formalization target: finite-measure convolution, local finite-order products, Stirling-number composition, Fourier-to-Chebyshev transfer, and uniform C² summation. No stronger endpoint or algorithmic claim follows automatically from its completion.
