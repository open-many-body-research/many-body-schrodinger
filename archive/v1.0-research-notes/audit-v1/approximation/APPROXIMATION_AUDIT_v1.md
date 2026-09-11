> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Approximation-chain audit, version 1

Date: 2026-09-09. This is an independent paper-proof audit of the approximation dependencies of `RWA_REPORT.md`. No Lean build, numerical RATE experiment, new certificate computation, or executable ground-energy algorithm is supplied by this audit. **The actual physical global RATE and Theorem T remain unverified by this artifact.** The conditional approximation calculations below are supported by direct examination; agreement with an older audit is not being used as a proof premise.

All reads used `THEOREM_T_FREEZE_2026-09-09_212604/`. All writes used `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/approximation/`. The frozen snapshot and its original project paths were not modified. Frozen provenance is commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, annotated tag `theorem-t-proof-freeze-2026-09-09`. `PROVENANCE_v1.json` records exact relative paths, line counts, observed SHA-256 values, and their comparison with `FREEZE_MANIFEST.json`. Every one of the 12 inspected file hashes matched its manifest entry. This is a scoped source-integrity check, not a verification of the entire freeze.

## Outcome and verification boundary

No substantive counterexample or internal gap was identified in the **conditional** local Poisson approximation implication or the **conditional** global Poisson construction. Their exact nodes, ordinary-polynomial degree allocation, large-polynomial tails, physical six-dimensional H² conversion, telescoping identity, Hardy estimates, normalization, and stated conservative powers can be justified by the displayed calculations. This is a paper-proof assessment, not machine verification or exhaustive formal derivation of every estimate.

The strongest additional deduction made here is the explicitly conditional n^(1/10) RATE in `RATE_BALANCE_v1.md`, obtained by changing only the auxiliary outer radius from (q+1)^(1/16) to (q+1)^(1/10) in G24. That file gives the exact input formulas, schedule constraints, constants, polynomial absorption, all-index conversion and residual implication. It does not declare the actual ψ to satisfy its uniform-analyticity premises.

The following physical dependencies are not discharged by this audit: the scale-uniform factorial bounds in G1; the uniform exterior holomorphic charts in G2; full operator/ground-state/spectral identification in `TWO_ELECTRON_THEOREM.md`; and effective rational moments, optimization, stopping and bit complexity. Those files are assigned to separate audits. The tail estimate G3 was audited here as a deduction from actual continuum-domain/eigenfunction and hydrogenic-energy facts, with those underlying facts kept explicit.

## Complete text coverage and load-bearing checks

The following files were read in full. A line interval identifies mathematical material assessed here; it does not claim that a cited external proof was also read in its entirety.

| Frozen relative path | Coverage and conclusion |
|---|---|
| `RWA_REPORT.md` | Entire report. Approximation statements (3), (6), (7), dependency claims 4–6 and their use in Theorem T checked against the linked proofs. Analytic and effective-composition assertions remain outside this subaudit. |
| `rwa_proof/DYADIC_REMAINDER_ATTEMPT.md` | Entire D1–D21 and scope discussion. Direct check of the conditional local theorem, shell polynomials, windows, physical norm, all tails, exact index and small indices. |
| `rwa_proof/DYADIC_REMAINDER_AUDIT.md` | Entire audit. Recomputed central identities/inequalities independently instead of accepting its verdict. |
| `rwa_proof/GLOBAL_DYADIC_ATTEMPT.md` | Entire G1–G27. G1–G3 retained as inputs; G5–G27 checked as a conditional chain. |
| `rwa_proof/GLOBAL_DYADIC_AUDIT.md` | Entire audit. Approximation and tail checks reproduced; its assessment of `EXTERIOR_ANALYTIC_ATTEMPT.md` is not independently certified here. |
| `dyadic_proof/LEADING_SINGULARITY_THEOREM.md` | Entire L1–L15, graph bound and scope. Component combination, physical multiplier, Hardy matrix and dictionary membership checked. |
| `dyadic_proof/DYADIC_RADIAL_LEMMA.md` | Entire R1–R10 and coefficients section. Frullani representation, Taylor remainder, factorial integral, panels, omitted scales and index checked. |
| `dyadic_proof/ANGULAR_LEMMA.md` | Entire A1–A14, polynomial witness and height discussion. Angular derivatives, Laplace identity, Banach-valued Taylor circle, growing angular order, tails and rational coefficients checked. |
| `dyadic_proof/EXTERIOR_CONSTANTS.md` | Entire X1–X7. Weighted first derivative, domain/product step, graph estimate and inverse-weight matrix checked, conditional on domain/eigenfunction facts. |
| `dyadic_proof/ADVERSARIAL_AUDIT.md` | Entire audit. Rechecked relevant angular/radial/leading/tail claims; old finite-exponent obstruction is not independently re-proved here. |
| `dyadic_proof/PHYSICAL_REGULARITY_AUDIT.md` | Entire P1–P11. Leading coefficient and extraction, collision-cone geometry, IMS form bound and weighted tail checked. Its qualitative pair-chart discussion is consistent with the source statements; uniform analytic estimates are expressly not supplied there. |
| `CORRECTION_PROTOCOL.md` | Entire preservation/correction protocol. No frozen original was corrected and no completed erratum was sealed by this subaudit. |

References to `RWA_THEOREM.md`, `UNIFORM_ANALYTIC_AUDIT.md`, `EXTERIOR_ANALYTIC_ATTEMPT.md`, `EXTERIOR_ANALYTIC_AUDIT.md`, `TWO_ELECTRON_THEOREM.md`, `RATE_DICTIONARY_DECISION.md`, `helium/THEORY.md`, `THEOREM_T_COMPOSITION.md`, and `THEOREM_T_AUDIT.md` identify **boundary dependencies**, not additional files fully audited here. This distinction prevents a coverage list from implying more verification than occurred.

## Local shell approximation

The statement D1–D2 is about a reduced, exchange-symmetric function satisfying an all-order factorial estimate with compatible analytic boundary germs. On the fixed shell K={a,b,c≥0:1/4≤S≤2}, rescaling by τ gives a fixed holomorphic radius and amplitude. The Taylor estimate uses the multinomial identity Σ_{|ν|=k} k! h^ν/ν!=(h₁+h₂+h₃)^k; mere pointwise analyticity would not suffice. This distinction is respected by D1 and lines 34–40.

The cutoff construction at lines 64–97 is used only to construct ordinary polynomial coefficients. For h(t)=exp(−1/t), the circle radius t/2 gives |h^(k)(t)|≤k!(2/t)^k exp(−2/(9t)), whose maximum is at most 9^k(k!)². The step normalization follows by integrating over [1/4,3/4], where 1/t+1/(1−t)≤16/3<6. Telescoping weights χ_i∏_{h<i}(1−χ_h) sum to one on the shell and avoid division by a small partition denominator.

Composition with cosines preserves Gevrey order two. Integrating in a largest Fourier-frequency direction and choosing derivative order proportional to √frequency gives exp(−b√frequency). A tensor truncation of degree d in each of three variables has total degree at most 3d. Two physical polynomial-coordinate derivatives cost at most fourth powers of frequency. The absolute weighted coefficient series is summable. Thus the same polynomial simultaneously approximates on the shell and has a degree-independent derivative bound on its containing cube.

Outside the cube, lines 101–106 bound Chebyshev derivatives by C(k+1)^(2i)(1+2|x|/B)^k with B≥4. In the nonnegative cone each coordinate is at most t=S; for t≥2, 1+2t/B≤t. The stated bound M(q+1)^4(6t)^q is conservative. There is no untracked q^q factor or new exponential node here.

The exact identity E_k′(z)=−e^(−z)z^k/k! gives positive windows and telescoping. The gamma density increases before z=k and decreases after it. Differentiation introduces only polynomial factors in k,t. For I(t)=t−1−log t,

\[
I(2t)\ge1/8+\tfrac12\log(1/(4t))\quad(t\le1/4),\qquad
I(t)\ge1/4+\log(t/2)\quad(t\ge2).
\]

These follow by differentiating the differences and using 2/3<log2<3/4. The retained lower-tail power compensates all inverse powers at zero. The upper-tail scalar integral is exactly 2^14/(2k−2q−14), when k>q+7. With k=256(q+1), the factor 12^q exp(−k/4) after taking the square root is exponentially small. Integrating a bound beyond the local target's domain in D17 is legitimate because only the polynomial/majorant is extended, not the physical f.

The local witness is in V_{769q+770} exactly: k=J=256(q+1), the degree is at most k+q, and the last node index is J+1. The separately approximated constant uses the original base node and respects the budget. The finite number of small indices can use zero. This theorem alone supplies no small global error; its constant approximant has mass out to order k/Z, as the frozen proof explicitly notes.

## Physical H² conversion and domain membership

The physical Cartesian derivatives of the distance coordinates have bounded first derivatives and second derivatives with norms √2/r, √2/s and 2√2/u. The required angular integrations are

\[
\int G(S)\,dx=\frac{8\pi^2}{15}\int_0^\infty G(S)S^5\,dS,
\]
\[
\int G(S)/r^2\,dx=\int G(S)/s^2\,dx
=\frac{16\pi^2}{3}\int_0^\infty G(S)S^3\,dS,
\]
\[
\int G(S)/u^2\,dx=\frac{16\pi^2}{9}\int_0^\infty G(S)S^3\,dS.
\]

For the last identity, integration over relative angle gives 8π²/(rs) log(S/|r−s|); after r=vS, the remaining integral is ∫₀¹v(1−v)log(1/|2v−1|)dv=2/9. These establish the physical scaling τ^(σ+1) for second derivatives and τ^(σ+3) for zeroth order. On growing shells the factor τ^(σ+1)(1+τ²) is therefore necessary and is included in G15–G18.

The weak-derivative argument is essential and is present at D198: away from the vertex, flux across a radius-ε pair tube is O(ε²) when reduced first derivatives are bounded. At total collapse it is O(ε^(σ+4)), since the physical gradient is O(ρ^(σ−1)) and the five-dimensional sphere has area O(ε⁵). These vanish. The first-derivative boundary terms are easier. Thus the locally square-integrable classical Hessian agrees with the weak Hessian. This argument also applies to finite distance-polynomial exponentials. It does not justify arbitrary collision behavior for N>2.

## Leading radial/angular logarithm and physical multiplier

The radial representation R2 follows by splitting Frullani's integral at Z/2 and setting λ=Z+t. The allowed-node panels [3a_j/4,3a_j/2] are contiguous and have |λ−a_j|/b≤1/2 for b=a_j+min(λ−a_j,0). Differentiating the integral Taylor remainder gives R6 through order two. The factorial integral R7 and its use in R8 preserve the scale a_j^(−3); the additional derivatives are paired with corresponding powers of S in R4. The panel weights are bounded by log4, their inverse-cubic node scales form a geometric sum, and the omitted integral is bounded by ∫_L^∞λ^(−4)dλ. The exact total degree is k+2 at node j, as required. The radial witness has real coefficients involving logarithms and a fixed Euler-constant expression; it is not a rational certificate.

For the angular part, log(ρ/S)=−(1/2)Σ_{k≥1}(2rs/S²)^k/k, with 2rs/S²≤1/2. The factor q=x₁·x₂ cancels the apparent pair-axis inverse-distance terms in the Cartesian Hessian. Absolute convergence of the H² norm series identifies it with the physical logarithm. Each inverse power S^(−2k) is removed by its Laplace integral before constructing the witness. The Taylor parameter circle of radius 3λ_j/4 lies in Re λ>0 and contains every selected panel with ratio at most 2/3. Its Bochner norm bound is integrable after the Laplace weight; the tail is again λ^(−4).

The factorial ratio bound A10 follows by separating 15 final factorial factors and using the central-binomial inequality. With K=m, P=16m, J=4m, the factors 72^K(2/3)^(P+1) and 32^K2^(−3J) decay; 72(2/3)^16<1/8. The exact index is 26m+2. The angular coefficients are integrals of ordinary polynomials over rational endpoints, hence rational for integer Z; this algebraic fact does not depend on floating-point quadrature.

In the leading theorem, adding the radial and angular witnesses uses the **same** index N. Multiplication by the ordinary degree-L Taylor polynomial in u/2 adds L to that degree and leaves all nodes unchanged. The physical Hessian contribution 1/u is controlled by sliced Hardy. The matrix in L13 has squared Frobenius norm 87/4<25; hence the bound 5e^(D/√2) is valid. Taylor truncation through two scalar derivatives, followed by the same Hardy estimate, gives L14. Taking N=⌊n/2⌋ and L=⌈n/2⌉ produces the stated local rate. Its graph estimate uses nested balls and a cutoff only for Hardy; that cutoff does not become part of the witness.

These calculations support the explicit leading-component approximation as mathematical paper arguments. They do not prove uniform analytic regularity for the nonconstant physical remainder or any normalized ground-state certificate.

## Physical tail

P9 uses the IMS partition η₁=r/ρ, η₂=s/ρ. Their squares sum to one and Σ|∇η_i|²=ρ^(−2). Applying a one-electron hydrogenic lower bound in each complementary coordinate and dropping nonnegative repulsion gives

\[
\mathfrak h_Z[f]\ge[-Z^2/2-3Z/(2R)-1/(2R^2)]\|f\|_2^2
\]

for functions supported in ρ≥R. The attractive remainder is exactly −ZS/ρ² and S≤3ρ/2. This is a continuum form inequality, not a matrix truncation argument.

Using E_Z≤−Z²+5Z/8 and Z≥2 gives an ionization margin at least 3Z²/16. At R₀=32/Z the exterior correction is 97Z²/2048. Subtracting the cost a²=Z²/16 of a=Z/4 leaves 159Z²/2048. The weighted ramp calculation in P10 therefore yields ||e^(aρ)ψ||₂²≤161·3³²/159. Truncating the exponential weight before testing the eigenvalue equation avoids an unbounded-test-function assumption.

The proof of X4 correctly uses 2√2 Z||∇v||||v||≤||∇v||²/4+8Z²||v||². This leads to ||e^(aρ)∇ψ||₂≤6Z√K₀. For W=e^(a√(1+ρ²)), the product formula makes H_Z(Wψ)∈L² while Wψ∈H¹. Identifying this with the closed-form operator domain is the explicit load-bearing domain fact; it must ultimately be proved in the continuum Lean development.

X7 uses ||D²v||₂=||Δv||₂ for the full Frobenius Hessian by Plancherel, and ||∇v||²≤||v||||D²v||. The resulting coefficients 6 and 6b²+2 are conservative. The inverse-weight product matrix has squared Frobenius norm 3+5a²+(a√6+a²)², agreeing with X1. Consequently the S-tail exponent is γ=a/√2=Z/(4√2), because S≤√2ρ. This controls the actual ψ only; it does not control a polynomial-exponential approximant fitted on a ball.

## One global witness and normalized residual

G5 is a legitimate global *finite-order* envelope. Exterior Cauchy bounds cost (1+S)^i for i≤2; the proposed S^(σ−i)(1+S)^4 dominates this at large S. It is not an all-order global version of G1.

The normalized shell radius loss in G6 is at most (1+T)^(−2). With O(h^(−3)) analytic boxes, telescoping Gevrey weights have derivative scale O(h^(−4)); undifferentiated factors are bounded by one, so no constant is raised to the number of boxes. The prefactor M₀ is O(h^(−3)). Fourier coefficients decay with parameter at least c h². Counting the O(k²) frequency triples and two derivatives leads to a sixth-power moment; substituting t=√k gives degree 13 and therefore the fourteenth inverse power of h². This yields h^(−31)=(1+T)^62, as stated in G7–G9. Constants hidden in these estimates depend on G1/G2 and a fixed cube, not on T or q.

The global witness uses ψ₀E_k at **the same outer node** as the telescoping window sum. Direct expansion yields

\[
\psi-v_q=\psi(1-E_{\mathrm{out}})+
(\psi-\psi_0)E_{\mathrm{in}}+
\sum_jW_{j,k}(f-P_j).
\]

The outer omitted function is the decaying ψ; using f there would leave a false constant plateau. The global proof includes the exterior of the actual fitted polynomials, whose growth is bounded by (6t)^q. Its worst enlarged scalar integral is exactly

\[
12^{2q}e^{-k/2}\int_2^\infty t^{21}(t/2)^{2q-2k}\,dt
=12^{2q}e^{-k/2}\frac{2^{22}}{2k-2q-22}.
\]

The zero-order target power before integration is at most t^(σ+7); after squaring and multiplying by six-dimensional volume it is t^(2σ+19)≤t²¹. Polynomial terms are no worse. Higher derivatives have smaller powers. The chosen k=256(q+1) absorbs 12^q and all remaining degree growth. Summing τ_j^(σ+1)(1+τ_j²) gives C(1+T)^4, yielding the exponent 66 in G24.

The inner omission has small scale τ_*^(σ+1) because f vanishes with positive order. In the outer omission, the physical Hessian of S introduces ψ/r and ψ/s. For S≥T/8 these are controlled by Hardy applied to χψ, where χ vanishes below T/16 and equals one above T/8. The cutoff is used only in the estimate. The actual tail of ψ then supplies exp(−γT/16). The window's first two derivative norms cost only polynomial powers of the Poisson order and T^(−1).

For the frozen schedule T=(q+1)^(1/16), the shell exponential has power q^(1/4) while the outer physical tail has power q^(1/16); every prefactor is polynomial. This establishes the claimed conditional G24→G25 implication. The sharper balance in `RATE_BALANCE_v1.md` uses the same calculation with a different admissible T.

Finally ||(H_Z−E_Z)e||₂≤(√6/2+4Z+2+Z²)||e||_{H²_*} follows from the trace inequality and sliced Hardy, with |E_Z|≤Z². Eventual L² error ≤1/2 makes ||v_n||₂≥1/2, permitting normalization without destroying the RATE. It is an actual continuum residual. Identifying E_Z with the bottom of the complete fermionic spectrum and turning a residual into certified intervals are separate spectral and algorithmic obligations.

## Primary-literature comparison and novelty discipline

The cited [Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Sørensen 2005 paper](https://arxiv.org/pdf/math-ph/0312060), Theorem 1.1, equations (1.8)–(1.12), was inspected in the primary PDF. It supplies ψ=e^(F₂+F₃)Φ with Φ∈C¹,¹ and universal quadratic logarithms for general Coulomb systems. Substituting y_i=2x_i changes its kinetic coefficient to the one in this project and yields κ_Z=Z(2−π)/(3π); the extra log4 factor is smooth. It supplies neither G1 nor the exact-dictionary RATE. The local subtraction of κ_Zψ(0)q logρ² follows from that factorization and elementary product estimates, not an infinite Fock expansion.

The primary [2008 analytic-structure paper](https://arxiv.org/pdf/0806.1004), Theorem 1.4 and collision sets (1.8)–(1.10), was also inspected. It gives analytic-plus-distance decompositions near **isolated** pair collisions. Its domain excludes simultaneous collisions. A bound uniform under approaching a simultaneous collision is additional mathematics and cannot be attributed to its theorem statement. This applies directly to the distinction between G1 and qualitative pair analyticity.

For comparison, [Maday–Marcati, arXiv:1912.07483v2](https://arxiv.org/pdf/1912.07483), introductory equation (1), Section 2 and the descriptions of Theorems 2–3, treats d=2,3 nonlinear scalar Schrödinger equations with isolated point singularities and hp discontinuous Galerkin approximation. Its dimension, principal operator, singular set, periodic setting and approximation spaces differ from the present reduced continuum problem. It is relevant precedent for weighted regularity and exponential approximation; it is not an applicability shortcut to this dictionary or a source of a verified bit-cost theorem here. Only these portions of that primary paper were inspected, not its complete proof.

The leading-factor regularity and isolated-pair structure are established literature results. The dyadic panel, Poisson-window and degree-budget constructions are project-specific deductions from elementary analysis; this audit supports their explicitly conditional implications but does not establish priority. The improved 1/10 balance is a new deduction in this work package, with **novelty undetermined**. The search was bounded; failure to locate an exact match is not evidence of novelty. No unsupported broad efficiency claim follows from these approximation statements.

## Explicit outstanding obligations and no silent status upgrades

| Obligation | Exact frozen anchor | Status established by this audit |
|---|---|---|
| Uniform all-order vertex estimate for the actual state | `GLOBAL_DYADIC_ATTEMPT.md` lines 11–17, G1; `RWA_REPORT.md` lines 15–24 | Required input, not discharged here. C¹,¹ and isolated-pair analyticity do not suffice. |
| Uniform exterior ordinary-distance holomorphic charts | `GLOBAL_DYADIC_ATTEMPT.md` lines 19–23, G2; report line 135 | Required input, not discharged here. The older global audit's approval is not proof evidence in place of the analytic derivation. |
| Actual operator domain and ground/symmetry facts | `EXTERIOR_CONSTANTS.md` lines 91–93; `LEADING_SINGULARITY_THEOREM.md` lines 10–21 | Used explicitly, independently assigned for spectral audit and Lean formalization. |
| Exact implementation of continuum norms and dictionary | D11–D12, G14, G26–G27 | Paper calculations checked; no Lean formalization of them is supplied here. |
| Executable coefficient recovery and rational certificates | `RWA_REPORT.md` lines 190–245 | Outside subaudit; existential shell polynomials are not a verified algorithm. |
| All claims of polynomial stopping/bit complexity | report equations (8)–(10) | Outside subaudit; neither 2256 nor any improved cost exponent is certified here. |
| N=3 and arbitrary N | isolated-collision exclusion and N=2 physical norm calculations above | No generalization established here. |

No mathematical error requiring an erratum was found within the conditional approximation chain assessed here. The frozen `PROVEN` labels are historical claims. Their unconditional physical conclusion is not reissued on the strength of this audit, and no theorem status is upgraded because two audits agree. A newly discovered error or a later change of disposition must be recorded in a separate versioned file with its own frozen-path/hash references.
