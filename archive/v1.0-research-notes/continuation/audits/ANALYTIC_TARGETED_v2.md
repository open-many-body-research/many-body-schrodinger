> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Targeted analytic-to-approximation improvement, version 2

Date: 2026-09-09. Evidence: **conditional paper theorem with a self-contained new approximation lemma; not Lean verified, not a numerical certificate, and not an executable coefficient algorithm.**

The new result is a conditional approximation theorem in the **unchanged two-electron dictionary**. For each fixed integer κ≥1, the explicit vertex analyticity, exterior analyticity, and physical H²-tail assumptions below imply an error

\[
\|\psi-v_n\|_{H^2_*}\le C_\kappa
 \exp[-c_\kappa n^{\kappa/(3\kappa+1)}].
\tag{A0}
\]

Thus every fixed exponent strictly below 1/3 is available conditionally. The first case is 1/4. The endpoint 1/3 is **not** proved. Constants depend on κ, with no control as κ→∞. This does not prove that the actual Coulomb ground state satisfies the assumptions, or upgrade Theorem T's verification status.

The specific improvement concerns the Gevrey extension step in frozen `rwa_proof/GLOBAL_DYADIC_ATTEMPT.md`, G9, lines 88–104. Its cover-cardinality factor in the derivative parameter is unnecessary if the chart cutoffs have uniformly bounded overlap. The original estimate is conservative rather than false. No confirmed inherited error was found in this targeted step; no correction entry is required. The new theorem changes the auxiliary approximation construction and its outer-radius schedule, and is separately identified by this file. It does not change the trial dictionary, Hamiltonian, physical domain, or target function.

## 1. Provenance and scope

All frozen paths below are relative to `THEOREM_T_FREEZE_2026-09-09_212604/`, frozen Git commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag `theorem-t-proof-freeze-2026-09-09`. The following SHA-256 values were recomputed and matched `FREEZE_MANIFEST.json`.

| Frozen relative path | SHA-256 | Scope used here |
|---|---|---|
| `RWA_REPORT.md` | `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066` | Report and dependency/verification claims; read in full. |
| `rwa_proof/GLOBAL_DYADIC_ATTEMPT.md` | `b5f6ff9a59921f107467f1112a1f744323c7b2250173eb03f6e99309441aed1b` | Read in full; target G6–G9, substitute into G15–G24. |
| `rwa_proof/DYADIC_REMAINDER_ATTEMPT.md` | `bb30295c982758a93237b583a6d52d3490c49b0d8f0737036faa4e701d997b02` | Lines 1–200: original cutoff construction, Chebyshev conversion, Poisson bounds, physical H² conversion/removability. |
| `CORRECTION_PROTOCOL.md` | `1bdb5c1b27de5eaf21b635b08581131c84f4436cff342b45f67fae8f82db2bb3` | Read in full. |

The prior `AUDIT_2026-09-09_v1/analytic/ANALYTIC_AUDIT_v1.md`, `approximation/APPROXIMATION_AUDIT_v1.md`, and `approximation/RATE_BALANCE_v1.md` were consulted to avoid repeating the broad analytic audit. The latter proves the conditional 1/10 schedule consequence of the **old** G24 bound. Here a new local extension estimate changes that bound. No new audit of the weak KS pullback, Grušin recurrence, physical ground branch, or exact moment algorithms is claimed.

Primary-source comparison was limited: the publisher's article *On the eigenvalue distribution of spatio-spectral limiting operators in higher dimensions* was located as potentially relevant to Gevrey cutoff estimates, but [the publisher page](https://www.sciencedirect.com/science/article/am/pii/S1063520323001070) returned HTTP 403 when opened. It is not a proof dependency and its full result was not assessed. The argument below derives its needed Gevrey estimates directly. There is no novelty claim.

## 2. Exact hypotheses and objects

Electron count is N=2. Approximation order is n. Requested computational precision p does not occur in this theorem. The auxiliary shell degree is q, the Poisson order is k, and κ is a fixed cutoff-shape parameter.

Fix Z≥2. For physical points (x₁,x₂)∈R⁶, put r=|x₁|, s=|x₂|, u=|x₁−x₂| and S=r+s. Half-perimetric coordinates satisfy r=b+c, s=a+c, u=a+b, so S=a+b+2c. Let ψ be a real rotation-invariant and exchange-symmetric physical function of norm one in L²(R⁶), continuous at the origin, and let f=ψ̂−ψ₀ denote its reduced representative minus its origin value. Assume:

1. For some fixed positive Cᵥ,Aᵥ,δᵥ and 0<σ<1,
   \[
   |\partial^\nu f|\le C_v A_v^{|\nu|}|\nu|!S^{\sigma-|\nu|}
   \quad(0<S<\delta_v),
   \tag{A1}
   \]
   with compatible analytic germs across all nonvertex boundaries of the closed octant.
2. For some fixed 0<d<δᵥ/8 and c_d,M_d>0, every closed-octant point with S≥d has compatible holomorphic extensions to the complex polydisc of radius c_d/(1+S), bounded there by M_d. Compatibility means the extensions agree wherever their germs continue the same physical reduced function. This is frozen G2 as an explicit assumption.
3. ψ∈H²(R⁶), and for fixed C_t,γ>0,
   \[
   \|\psi\|_{H^2_*(S>R)}\le C_t e^{-\gamma R}\quad(R\ge1).
   \tag{A2}
   \]
   Here the physical H²_* norm counts L², the Euclidean gradient, and the full Frobenius Hessian, including both ordered mixed entries.

The target dictionary is exactly

\[
V_n^{(Z)}=\sum_{j=0}^{\lfloor n/2\rfloor}
e^{-Z2^jS}\mathcal P_{n-2j}^{\mathrm{sym}}(r,s,u).
\tag{A3}
\]

Symmetry is r↔s (equivalently a↔b). The two polynomial coordinate systems are related by an invertible linear map and have the same degree filtration. Tensoring an exchange-symmetric spatial member with the unit spin singlet gives an element of the full fermionic spin-space under simultaneous exchange of coordinates and spins. That tensoring changes none of the norms in this theorem.

These hypotheses are about the actual functions. They do not supply their own proofs. In particular (A1) is a quantitative all-order estimate, not merely pointwise real analyticity.

## 3. Bounded-overlap Gevrey extension lemma

Let K={y≥0:1/4≤S(y)≤2}. Suppose a function F has compatible holomorphic polydiscs of one radius 0<h≤1/100 at each point of K, with sup norm at most M on each disc. For any fixed integer κ≥1, put

\[
\mathfrak{s}=1+1/\kappa>1.
\]

Then there is a real C∞ function G, compactly supported in the fixed cube [−4,4]³, agreeing with F in a real neighborhood of K, such that

\[
\|\partial^\nu G\|_\infty
\le C_\kappa M(C_\kappa/h)^{|\nu|}(|\nu|!)^{\mathfrak{s}}.
\tag{A4}
\]

The constants depend on κ and fixed dimension, **not** on h, chart count, or F. The proof follows.

### 3.1 A cutoff of any fixed order 1+1/κ

Define H(t)=exp(−t^(−κ)) for t>0 and H(t)=0 for t≤0. For a positive real t, take a complex circle of radius t/(8κ). On its disc, |arg z|≤1/(4κ), |z|≤(1+1/(8κ))t, and therefore Re(z^(−κ))≥1/(4t^κ). Cauchy's estimate gives, for m≥1,

\[
|H^{(m)}(t)|\le m!(8\kappa/t)^m e^{-1/(4t^\kappa)}.
\]

Maximizing t^(−m)exp(−1/(4t^κ)) and using m!≥(m/e)^m yields

\[
\|H^{(m)}\|_\infty
\le [8\kappa(4/\kappa)^{1/\kappa}]^m(m!)^{1+1/\kappa}.
\tag{A5}
\]

All derivatives tend to zero at t=0. Thus H is C∞ with zero jets there; this justifies its extension, rather than presuming smoothness across zero.

The function w(t)=H(t)H(1−t) is supported in [0,1]. Its integral I is positive: on [1/4,3/4], w≥exp(−2·4^κ), so I≥exp(−2·4^κ)/2. The normalized integral

\[
\Theta(t)=I^{-1}\int_{-\infty}^t w(v)\,dv
\]

is zero on t≤0, one on t≥1, and takes values in [0,1]. Leibniz's rule, (A5), and integration show |Θ^(m)|≤C_κ^m(m!)^𝔰 for m≥1 after enlarging C_κ. Therefore

\[
\rho(t)=\Theta(t+2)\Theta(2-t)
\]

is supported in [−2,2], is identically one on [−1,1], takes values in [0,1], and has |ρ^(m)|≤C_κ^m(m!)^𝔰. It is flat at its support boundaries. Huge dependence on κ is allowed and retained in C_κ.

### 3.2 Geometry and the number of active jets

Set ℓ=h/16 and use the lattice ℓZ³. Retain exactly the finitely many lattice centers c_j whose closed half-cell {y:|y−c_j|∞≤ℓ/2} intersects K; choose x_j in that intersection. Let

\[
\chi_j(y)=\prod_{i=1}^3\rho((y_i-c_{j,i})/\ell).
\]

Their inner cubes cover K, and the sum construction below equals one on its ℓ/2-neighborhood. Every support satisfies |y−x_j|∞≤(5/2)ℓ< h/4. Hence the analytic chart F_j centered at x_j is available on a strict neighborhood of that support, and Cauchy's derivative estimates there retain radius at least h/2. There is no evaluation of an analytic chart outside its domain.

At any real point y, at most 5³=125 lattice supports can contain y: each coordinate interval of length 4ℓ contains at most five lattice coordinates. At a support boundary the cutoff and all its derivatives vanish. Thus **at every derivative order**, the set of factors whose jets can contribute has cardinality at most L=125. This pointwise jet statement, rather than just an order-zero support count, is the fact needed by Leibniz's rule.

Order the retained centers in any fixed way and set

\[
\beta_j=\chi_j\prod_{i<j}(1-\chi_i),\qquad
G=\sum_j\beta_jF_j,
\tag{A6}
\]

each summand extended by zero off its own analytic chart. It is smooth because χ_j is flat at the support boundary and that support lies strictly inside the chart. The weights are nonnegative, and the telescoping identity gives Σβ_j=1−∏(1−χ_j)≤1. In a neighborhood of K at least one χ_j=1, so the sum equals one. Compatible analytic germs then give G=F there.

For derivatives of order m at y, all inactive factors (1−χ_i) have value one and zero positive-order jets; they create no factor depending on the total chart count. If an earlier factor has value zero and every derivative zero, that entire product contributes zero. At most L weights have nonzero jets at y, and each has at most L nontrivial cutoff factors in its jets. For a product of at most L+1 factors, multinomial Leibniz, ∏m_i!≤m!, and the sum of multinomial coefficients ≤(L+1)^m bound its m-th derivatives by

\[
M\,[C_\kappa(L+1)/h]^m(m!)^{\mathfrak{s}}.
\]

The single analytic factor has Cauchy bound M(2/h)^m m!, which fits the same estimate since 𝔰≥1. Summing at most L contributing weights proves (A4). At order zero, |G|≤M follows directly from nonnegative weights and Σβ_j≤1. All supports lie in [−4,4]³. This proves the extension lemma.

## 4. Polynomial lemma with exact h dependence

For q≥0 the preceding G has a real polynomial Q_q of total degree at most q satisfying

\[
\max_{|\nu|\le2}\sup_K|\partial^\nu(F-Q_q)|
\le C_\kappa M h^{-7}\exp[-b_\kappa(hq)^{1/\mathfrak{s}}].
\tag{A7}
\]

On the nonnegative cone, with t=S(y), the **same polynomial** obeys

\[
\begin{array}{ll}
|\partial^\nu Q_q(y)|\le C_\kappa M h^{-7},&0\le t\le2,\\
|\partial^\nu Q_q(y)|\le C_\kappa M h^{-7}(q+1)^4(6t)^q,&t\ge2,
\end{array}
\quad |\nu|\le2.
\tag{A8}
\]

Take g(θ)=G(4cosθ₁,4cosθ₂,4cosθ₃). It is smooth, periodic and even in each variable. For differentiation m times in one angular coordinate, grouping the chain rule by the number j of differentiated factors and dropping denominators in the cosine derivatives gives

\[
|\partial_{\theta_i}^m g|
\le C_\kappa M m!\sum_{j=1}^m
(C_\kappa/h)^j(j!)^{\mathfrak{s}-1}\binom{m-1}{j-1}
\le C_\kappa M(C_\kappa/h)^m(m!)^{\mathfrak{s}}.
\tag{A9}
\]

This estimate is uniform in the other variables. The last inequality uses j!≤m! and absorbs the geometric binomial sum into a constant to the power m. In particular it does not replace h^(−1) by h^(−𝔰) or introduce a cover-cardinality loss.

Integration by parts in a largest-frequency direction bounds its Fourier coefficient of maximum frequency R by C_κ M(C_κ/h)^m(m!)^𝔰 R^(−m). Taking

\[
m=\left\lfloor(hR/(2C_\kappa))^{1/\mathfrak{s}}\right\rfloor
\]

and using m!≤m^m gives coefficient decay C_κ M exp[−b_κ(hR)^(1/𝔰)]. The bounded set hR≤2^(𝔰+1)C_κ is absorbed by increasing the constant, so the bound is valid for every frequency. Evenness turns the series into a tensor Chebyshev series.

There are at most C(R+1)² frequency triples with maximum R. Coordinate derivatives of total order at most two cost at most C(R+1)^4, using the first- and second-derivative bounds for T_R on [−1,1]. Therefore the C² tail beyond tensor degree D is bounded by

\[
C_\kappa M\sum_{R>D}(R+1)^6e^{-b_\kappa(hR)^{1/\mathfrak{s}}}
\le C_\kappa M h^{-7}e^{-b_\kappa(hD)^{1/\mathfrak{s}}/2}.
\tag{A10}
\]

For the last inequality reserve half the exponential for the tail factor. The remaining sum is bounded by a constant times

\[
\int_0^\infty (x+1)^6 e^{-b_\kappa(hx)^{1/\mathfrak{s}}/2}\,dx
\le h^{-7}\int_0^\infty(u+1)^6e^{-b_\kappa u^{1/\mathfrak{s}}/2}\,du.
\]

The final integral is finite, depending on κ but not h. This explains why the loss is h^(−7) for every fixed 𝔰: changing Gevrey order does not alter this power. Choosing D=⌊q/3⌋ gives total degree at most q and proves (A7) for q≥6; the finitely many smaller q use Q_q=0 and the direct Cauchy estimates, enlarging the same h^(−7) bound.

The whole weighted coefficient series has the same h^(−7) bound, proving the bounded-cube part of (A8). Outside the cube, the elementary polynomial estimate

\[
|T_j^{(i)}(x/4)|4^{-i}
\le C(j+1)^{2i}(1+|x|/2)^j\quad(i\le2)
\]

and the coefficient-sum bound give the second part of (A8): on the nonnegative cone each coordinate is at most t, and 1+t/2≤t for t≥2. The larger base 6t is retained to match the frozen tail calculation. Finally average Q_q(a,b,c) and Q_q(b,a,c) if F is exchange symmetric. Since K, the cube, and t are invariant, all bounds and the degree are preserved.

## 5. Application to the physical shell family

Set F_τ(y)=τ^(−σ)f(τy), 0<τ≤T, T≥1. The explicit hypotheses in §2 imply, exactly as in frozen G6,

\[
h_T=c_h(1+T)^{-2},\qquad
\|F_\tau\|_{\rm hol}\le M_h,
\tag{A11}
\]

with fixed c_h,M_h>0, after shrinking c_h so h_T≤1/100. For sufficiently small τ this follows by the Taylor series of (A1) on the fixed normalized shell. On scales bounded below, the exterior hypothesis rescales its radius to at least c/[τ(1+2τ)], while τ^(−σ) is bounded; the fixed intermediate region is absorbed into the constants. Compatibility is an explicit premise in both ranges.

Applying (A7)–(A8) at h=h_T gives symmetric shell polynomials Q_{τ,q} of degree at most q with

\[
\max_{|\nu|\le2}\sup_K|\partial^\nu(F_\tau-Q_{\tau,q})|
\le C_\kappa(1+T)^{14}
\exp\left[-\frac{b_\kappa q^{1/\mathfrak{s}}}
{(1+T)^{2/\mathfrak{s}}}\right],
\tag{A12}
\]

and the growth estimates (A8) with C_κ(1+T)^14 in place of C_κMh^(−7). This **replaces** frozen G7–G9 in the new construction. It is a new proved paper implication of (A11), not an assumption that an audit supplies an approximation oracle.

## 6. Global witness, its tails, and the new bound

For q≥1 put k=J=256(q+1), choose any sufficiently large admissible T≥1, and assume

\[
k/T>Z,\quad 2^J\ge2k/(ZT),\quad T\ge16,\quad
\tau_*:=k/(Z2^{J+1})\le1,\quad2\tau_*<\delta_v.
\tag{A13}
\]

Let j₀ be the least index with a_{j₀}=Z2^(j₀)≥k/T. Then j₀≤J and T/2<τ_{j₀}≤T, where τ_j=k/a_j. Define

\[
E_k(t)=e^{-t}\sum_{l=0}^k t^l/l!,\quad
W_{j,k}(S)=E_k(a_jS)-E_k(a_{j+1}S),\quad
P_j=\tau_j^\sigma Q_{\tau_j,q}(\cdot/\tau_j),
\]

\[
v_q=\psi_0 E_k(a_{j_0}S)+\sum_{j=j_0}^J W_{j,k}(S)P_j.
\tag{A14}
\]

Its largest node index is J+1 and its largest degree at any node is k+q, hence v_q∈V_{k+q+2(J+1)}=V_{769q+770}. Smooth cutoffs appear only in the construction of the ordinary polynomial coefficients; they do not multiply the final vector. Finite distance polynomials times these exponentials lie in the physical H² domain: distance Hessians are bounded by constants times 1/r,1/s,1/u, square-integrable in the three respective transverse variables, with exponential decay at infinity.

The exact telescoping identity is

\[
\psi-v_q=\psi(1-E_k(a_{j_0}S))+fE_k(a_{J+1}S)
 +\sum_{j=j_0}^JW_{j,k}(f-P_j).
\tag{A15}
\]

The unchanged physical estimates G15–G23 apply with the new (A12) and polynomial-growth bound. The dependence can be checked term by term:

* On fitted shells, the physical C² conversion contributes (k+1)³τ_j^(σ+1)(1+τ_j²), and the new fitting factor is the right side of (A12).
* On the lower tail t≤1/4, the Poisson factor exp[−kI(2t)]≤exp(−k/8)(4t)^(k/2) absorbs the inverse powers in first and second derivatives. The global two-derivative envelope S^(σ−i)(1+S)^4 has at most (1+T)^4 there, absorbed by the new (1+T)^14 bound.
* On the upper tail t≥2, the same polynomial growth (6t)^q gives the same squared majorant as G16,
  \[
  12^{2q}e^{-k/2}\int_2^\infty t^{21}(t/2)^{2q-2k}\,dt
  =12^{2q}e^{-k/2}\frac{2^{22}}{2k-2q-22}.
  \]
  With k=256(q+1), its square root is at most C exp(−k/16). The new cutoff construction has not changed the polynomial's exterior growth class.
* The sum of shell norm scales is at most C_σ(1+T)^4. Consequently the total shell prefactor is now (1+T)^18, instead of (1+T)^66.
* The inner omission uses (A1), the global finite-order envelope, and gamma tails; it remains bounded by C(k+1)³τ_*^(σ+1).
* The outer omission uses (A2) and the same localized Hardy estimate for ψ/r and ψ/s. It remains at most C(k+1)³[exp(−k/16)+exp(−γT/16)] when T≥16. No new domain or sharp-indicator derivative is introduced.

The physical C² conversion and removability used here are D11–D12 and lines 196–198 of the frozen local proof; their finite-order formula is independent of the Gevrey order. The Poisson lower/upper tails and the physical tail/Hardy argument are reused as paper derivations, not as formalized lemmas. Their explicit premises have been retained.

Combining these estimates proves the new conditional construction bound

\[
\begin{split}
\|\psi-v_q\|_{H^2_*}\le
C_\kappa(k+1)^3(q+1)^4(1+T)^{18}\bigg[
&\exp\left(-\frac{b_\kappa q^{1/\mathfrak{s}}}{(1+T)^{2/\mathfrak{s}}}\right)
+e^{-k/16}\\
&+e^{-\gamma T/16}
+\left(\frac{k}{Z2^{J+1}}\right)^{\sigma+1}\bigg].
\end{split}
\tag{A16}
\]

This is a statement about one global admissible vector, including the tails of its actual polynomials.

## 7. Schedule optimization and every approximation order

Fix κ and set

\[
\theta=\frac1{\mathfrak{s}+2}=\frac{\kappa}{3\kappa+1},
\qquad T=(q+1)^\theta.
\tag{A17}
\]

All conditions (A13) hold eventually: k/T grows polynomially, T→∞, and the exponential 2^J dominates k while τ_*→0. This establishes a finite threshold q_* depending on the stated constants; the theorem does not claim that unknown physical regularity constants can be read by a program.

For q≥1, the shell exponent obeys

\[
\frac{b_\kappa q^{1/\mathfrak{s}}}{(1+T)^{2/\mathfrak{s}}}
\ge b_\kappa2^{-(2+2\theta)/\mathfrak{s}}
q^{(1-2\theta)/\mathfrak{s}}
=b_\kappa2^{-(2+2\theta)/\mathfrak{s}}q^\theta.
\tag{A18}
\]

The equality is exactly the balance (1−2θ)/𝔰=θ. The other exponentials in (A16) are bounded by exp(−16q^θ) and exp(−γq^θ/16). For the inner term use k≤2^(k/2) for every integer k≥4, which follows by induction from (k+1)/k≤5/4<√2. Since Z≥2 and J=k, it is at most exp[−128(σ+1)(log2)q^θ]. Thus the bracket is at most 4exp(−ηq^θ), where

\[
\eta=\min\{b_\kappa2^{-(2+2\theta)/\mathfrak{s}},16,
\gamma/16,128(\sigma+1)\log2\}>0.
\]

The prefactor is bounded by

\[
(k+1)^3(q+1)^4(1+T)^{18}
\le257^3 2^{18}(q+1)^{7+18\theta}.
\tag{A19}
\]

Writing x=q^θ, the remaining power of q is x^β with

\[
\beta=(7+18\theta)/\theta=7\mathfrak{s}+32=39+7/\kappa.
\]

Since sup_{x≥0}x^β exp(−ηx/2)=(2β/(eη))^β, (A16) gives C′_κexp(−ηq^θ/2) after enlarging the constant. This proves the stated stretched exponential without an unspecified polynomial-absorption step.

For all sufficiently large n let q=⌊(n−770)/769⌋. Then 769q+770≤n, and q≥n/1538 for n≥3078. For n≥769q_*+770 the admissible threshold holds. Dictionary nesting therefore gives (A0). For the finitely many smaller n choose zero and increase C_κ, using ψ∈H². For any fixed 0<α<1/3, choose an integer κ≥max{1,α/(1−3α)}. Then κ/(3κ+1)≥α and (A0) implies Ce^(−cn^α). No limiting process in κ is used.

## 8. Conditional continuum residual and limits

If, **in addition**, ψ is an eigenfunction on the actual H² domain of

\[
H_Z=-\tfrac12(\Delta_1+\Delta_2)-Z/r-Z/s+1/u,
\]

with eigenvalue E and |E|≤Z², sliced Hardy and the Laplacian trace inequality give

\[
\|(H_Z-E)e\|_2\le(\sqrt6/2+4Z+2+Z^2)\|e\|_{H^2_*}.
\]

Once ||ψ−v_n||₂≤1/2, the normalized φ_n=v_n/||v_n||₂ has residual at most twice this constant times the error in (A0), because (H_Z−E)ψ=0. For the finitely many smaller n use the normalized anchor exp(−ZS) and enlarge the constant. This is a conditional **physical** residual implication, with its eigenfunction/domain premise visible. It does not identify E with the bottom of the spectrum.

The improvement discharges one paper-level approximation prerequisite: constructing global shell polynomials with controlled derivative constants and their actual exterior growth. It leaves the physical assumptions (A1)–(A2), self-adjointness, spectral ground identification, rational coefficient generation, moment certificates, finite optimization, acceptance correctness, termination and bit complexity at their separate verification boundaries. Real Fourier/Chebyshev coefficients selected from ψ are not a runnable algorithm. No certified energy interval is emitted here, and no complexity theorem or performance claim is inferred.

The independent review of the exact new argument is recorded in `BOUNDED_OVERLAP_INDEPENDENT_AUDIT_v2.md`. Agreement is review evidence, not proof. The supporting `analytic_balance_checks_v2.py` checks selected rational exponent identities and dictionary index calculations; it is not a proof of the analytic theorem. Provenance and hashes are in `ANALYTIC_TARGETED_PROVENANCE_v2.json`. The next direct mathematical/formalization obligation is to encode (A4) with pointwise active-jet counting, or to discharge the physical uniform-analyticity hypotheses independently; no endpoint rate should be asserted in either path.
