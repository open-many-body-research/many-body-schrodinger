> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Full-wavefunction approximation audit: blow-ups, Gaussians, and mixed regularity

Audited 2026-09-09. This is a targeted primary-source audit for A–D in [tractable_target.md](nogo/tractable_target.md), not a proof that another algorithm cannot exist. **No Lean theorem is supplied here.** All mathematical literature results below have status **PROVEN (paper proof only)**. Interpretive deductions are identified separately. No numerical convergence experiment is promoted to a theorem.

## Finding

The sources below genuinely cover the full Coulomb wavefunction on configuration space, except for the explicitly excluded Bachmayr–Chen–Schneider result. They establish substantial regularity or conditional Gaussian approximability. None of their theorem statements gives the complete effective exponential H¹ approximation, polynomial construction, certified integration/conditioning, and validated eigenproblem algorithm required by A–D. The most consequential gap is not basis completeness: it is the quantitative conversion from regularity to an explicit accuracy-versus-bit-cost bound for the original unbounded-space eigenproblem.

## 1. Global weighted regularity, including intersections

**Ammann, Mougel, Nistor,** *A regularity result for the bound states of N-body Schrödinger operators: Blow-ups and Lie manifolds*, [arXiv:2012.13902v3](https://arxiv.org/abs/2012.13902v3), DOI [10.1007/s11005-023-01648-0](https://doi.org/10.1007/s11005-023-01648-0), Letters in Mathematical Physics 113:26 (2023).

Theorem 1.1: let F be a finite intersection-closed family of proper linear subspaces of X=Rⁿ containing {0}; form the iterated compactification X_F by blowing up their spheres at infinity and then their closures. Put δ(x)=min(dist(x,∪F),1). If

    V = Σ_(Y∈F) a_Y/d_Y + a_X,   a_Y∈C∞(X_F),
    u∈L²(X),   (Δ+V)u=λu on X\∪F distributionally,

then δ^|α| ∂^αu∈L²(X) for every multi-index α. Theorem 6.6 extends this to constant-coefficient elliptic operators and their defined inverse-square potentials.

For helium choose the collision planes x₁=0, x₂=0, x₁=x₂ and their intersection {0}. This includes triple coalescence and infinity. Multiplying Hψ=Eψ by −2 matches the displayed Laplacian sign convention.

The theorem states membership at every derivative order, without a factorial bound on the norms or an effective approximation-space construction. Remark 6.2 specifically corrects the compactification in the earlier paper's Theorem 4.2(ii): the Georgescu–Vasy compactification is needed. Read: §§1.1–1.2, Theorems 4.22, 6.1, 6.6 and proofs, Remark 6.2, Appendix A comparison of weights.

**Earlier result:** Ammann, Carvalho, Nistor, *Regularity for eigenfunctions of Schrödinger operators*, [arXiv:1010.1712v3](https://arxiv.org/abs/1010.1712v3), DOI [10.1007/s11005-012-0551-z](https://doi.org/10.1007/s11005-012-0551-z), LMP 101, 49–84 (2012). Theorem 4.3 gives u∈K_a^m for all m and a≤0 for Coulomb eigenfunctions. The introduction explicitly distinguishes its global weighted-Sobolev result from analyticity away from collisions and local simple-collision structure. It also anticipates further anisotropic regularity for numerical applications. The improved a<3/2 theorem in §4.2 is for **one electron**, so it cannot be substituted into a helium proof. Read: introduction, definitions of weights, Theorems 4.2–4.6 and their proof passages. Use the 2023 formulation above for the cleaner global conclusion and corrected geometric framework.

## 2. Anisotropic Gaussian theorem: strong but conditional

**Scholz, Yserentant,** *On the approximation of electronic wavefunctions by anisotropic Gauss and Gauss-Hermite functions*, [arXiv:1612.00360](https://arxiv.org/abs/1612.00360), DOI [10.1007/s00211-016-0856-4](https://doi.org/10.1007/s00211-016-0856-4).

Theorem 8.1 assumes f∈H¹(R³ᴺ) has a Gaussian expansion whose truncations satisfy error≤ε using at most (κ/ε)^(1/r) terms. For sufficiently small smoothing width, its substitute equation

    ũ + T̃ũ = f

has approximants with error≤ε and at most 2(2κ/ε)^(1/r) terms. The basis functions allow arbitrary positive-definite anisotropy matrices, centers and polynomial factors. Its application takes f=Qψ=K*ψ, a smoothed **unknown** eigenfunction, and fixes the eigenvalue in the resolvent. Equations (8.20)–(8.21) retain an additional original-versus-substitute error depending on smoothing width γ and quadrature step h.

The explicit contraction condition (8.9) depends on r; κ depends on f. Section 9 calls its algorithmic discussion preliminary. Read: §§1–4, operator estimates §§6–7, full §8 theorem/proof and §9. This is full configuration-space analysis, not orbital Hartree–Fock analysis.

**Deduction for A–D:** preserving each fixed algebraic approximation order does not bound κ(r), the cost of constructing f, or parameter growth as r and requested accuracy vary. Retaining a “negligible” fixed residual would fail arbitrary precision. Its quantitative residual may instead be driven to zero, but all induced costs and constants must then be reanalysed. Gaussian integral identities alone do not prove conditioning or certified bit complexity.

## 3. Mixed derivatives after explicit correlation

**Yserentant,** *The mixed regularity of electronic wave functions multiplied by explicit correlation factors*, ESAIM:M2AN 45, 803–824 (2011), DOI [10.1051/m2an/2010103](https://doi.org/10.1051/m2an/2010103), [primary full text](https://www.numdam.org/item/M2AN_2011__45_5_803_0.pdf).

For the full Coulomb eigenproblem let ψ₀=Σ_(i<j)φ(xᵢ−xⱼ) and u₀=e^(−ψ₀)u. The radial φ has a smooth nonnegative radial profile, bounded first derivative, second/third derivatives O(1/r) at infinity, and radial derivative 1/2 at zero. Define A={α:|αᵢ|≤1 for every electron i}. Theorem 6.6 proves D^αũ∈H¹ for α∈A in the modified negative-eigenvalue problem; Theorem 7.1 transfers allowed exponential weights to these derivatives of u₀. These are selected mixed derivatives, not arbitrary-order analytic estimates.

Section 9 additionally assumes φ bounded. Its explicit approximation count (9.6) is O(n^(3+ϑ)) terms for H¹ error O(1/n), for arbitrary fixed ϑ>0, invoking the earlier sparse-grid theory and physical antisymmetry. Read: §§1–4, Theorems 6.6/7.1–7.2 and proofs, §§9–10.

**Deduction:** this is valuable approximation with algebraic accuracy dependence; setting error≈2^(−b) gives a bound exponential in b. The exponent's independence of electron count does not control hidden constants in N or turn algebraic accuracy dependence into poly(b). Correlation also changes the integrals, as the paper acknowledges.

## 4. Recent global Barron regularity

**Yserentant,** *The regularity of electronic wave functions in Barron spaces*, [arXiv:2502.17950v3](https://arxiv.org/abs/2502.17950v3), revised March 18, 2026; ESAIM:M2AN 60 (2026), 689–699, DOI [10.1051/m2an/2026015](https://doi.org/10.1051/m2an/2026015).

With spectral Barron norm ∫(1+|ω|²)^(s/2)|û(ω)|dω, Theorem 4.7 gives membership for 0≤s<1 to negative-eigenvalue Coulomb H¹ solutions. In momentum notation,

    ||û||_(1,s) ≤ C₁ κ(2−s)||û||_(1,0),
    κ(2−s) = 2Γ((1−s)/2)/(√π Γ((2−s)/2)) ≤ 2/(1−s).

C₁ depends on total nuclear charge, N and eigenvalue, not s. The proof uses a high-frequency contraction and the low-frequency part of the eigenfunction. Hydrogen's exp(−|x|) supplies sharp failure at s=1. The article contains no exponential H¹ approximation algorithm or A–D complexity theorem. Read: full introduction, §§3–4 including all contraction lemmas and Theorem 4.7 proof; checked endpoint example. This is a genuine 2025/26 successor. The newer Ming–Yu arXiv:2608.22252 is audited separately by the coordinating agent.

## 5. Helium edge asymptotics do not include the triple corner

**Flad, Flad-Harutyunyan, Schulze,** *Explicit Green operators for quantum mechanical Hamiltonians. II. Edge type singularities of the helium atom*, [arXiv:1801.07552](https://arxiv.org/abs/1801.07552).

The model is the full Born–Oppenheimer two-electron Hamiltonian on R⁶. Theorem 1 supplies the Green-symbol expansion (3.1) through r², with O(r³) remainder, in localized weighted edge spaces and for weight 1/2≤γ≤3/2 as printed in its statement. The coefficients involve angular spectral projections and Mellin/Fourier operators applied to a localized eigenfunction. Sections 1.1 and 2 explicitly restrict the calculation to pair-collision edges. Section 1.1 leaves the triple-coalescence corner to subsequent work. Thus the expansion is neither a global convergent wavefunction series nor an effective H¹ error bound over R⁶. Read: §§1.1–1.2, construction synopsis §2.1, §3.1 Theorem 1 and accompanying scope comments. The long symbolic appendix was not independently recalculated. No assertion of machine verification is made.

## 6. Exponential Gaussian result with the wrong object

**Bachmayr, Chen, Schneider,** *Error estimates for Hermite and even-tempered Gaussian approximations in quantum chemistry*, Numerische Mathematik 128, 137–165 (2014), DOI [10.1007/s00211-014-0605-5](https://doi.org/10.1007/s00211-014-0605-5); primary preprint title *Numerical analysis of Gaussian approximations in quantum chemistry*, [full text](https://d-nb.info/1248220269/34).

Theorem 3.2 proves an H¹(R³) error C_(M,L)e^(−c√N) for finite-angular-momentum functions

    u(r,θ,φ)=Σ_(ℓ≤L, |m|≤ℓ) P_(ℓm,M)(r)e^(−γℓr) Ysolid_(ℓm)(r,θ,φ).

L and radial polynomial degrees M are fixed. Lemma 3.1 supplies explicit sinc estimates under inverse-Laplace strip analyticity and decay assumptions. This is not a theorem that the full helium ψ(x₁,x₂)∈H¹(R⁶) has that representation. The paper's model eigenproblem (2.1) is explicitly three-dimensional and uses an effective potential. Read: §§1–2, Theorem 3.2 and Lemma 3.1/proof. Extension to CI mentioned in the introduction does not supply full Coulomb correlation or truncation bounds. This theorem must not be cited as A for helium.

## 7. A–D ledger and precise logical limitation

| Obligation | What the audited sources supply | Missing for helium A–D |
|---|---|---|
| A: effective global exp(−cp) H¹ error | Global weighted derivatives; correlated mixed regularity; Gaussian transfer theorem | Controlled growth of approximation constants with accuracy, triple-collision-to-basis theorem, effective global decay/truncation contribution |
| B: constructible poly(p) dimension | Algebraic term counts; explicit individual Gaussian operations | Poly(b) count and bit construction from nuclear data, without the unknown state's smoothed expansion |
| C: certified matrices and conditioning | Closed Gaussian integral structure; awareness that correlation complicates integration | All-entry/norm error, rational precision, parameter bit-size and Gram conditioning bounds |
| D: certified lowest Ritz eigenpair | Variational and iterative formulations | Validated globally minimizing finite solve with an explicit polynomial bit bound under proved C |

**Elementary deduction (paper proof only):** “every algebraic order” does not logically imply stretched-exponential convergence. Let e_n=exp(−(log(n+1))²). For each r>0,

    n^r e_n ≤ exp(r²/4),

because r log n−(log(n+1))²≤r t−t²≤r²/4 for t=log(n+1). Yet for any fixed C,c,α>0, e_n≤Ce^(−c n^α) eventually fails: c n^α−(log(n+1))²→∞. This example is a statement about rate assertions, not a lower bound on helium approximation. It pinpoints why varying the Gaussian theorem's r requires uniform control of its constants.

The hand-waving temptations were to replace all-order smoothness by analyticity, read fixed-r arbitrary-order convergence as poly(log(1/ε)), discard a fixed substitution residual, replace the unknown smoothed eigenfunction by computable data, and transplant a three-dimensional orbital theorem into R⁶. Each was replaced by its exact hypothesis or marked as a missing result.

## Local primary-source archive

PDFs and pdftotext transcriptions are in [sources](helium_research/sources), with prefix `hp_`. File names preserve the original arXiv year; the verified versions and journal dates appear above. The archive also includes `hp_maday_marcati_2019.pdf`, passed to the independent approximation audit to avoid duplicated scope assessment. Search discovery snippets were not treated as theorem verification.
