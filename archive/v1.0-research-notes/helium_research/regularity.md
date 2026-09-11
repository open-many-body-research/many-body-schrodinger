> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Coulomb regularity audit for a certified helium approximation

Audited 2026-09-09 against the obligations A–D in [tractable_target.md](nogo/tractable_target.md). This document concerns the full wavefunction on configuration space. It supplies no Lean theorem and no numerical experiment. Established literature results have status **PROVEN (paper proof only)**; the August 2026 preprint is explicitly identified as such. The interpretation of their implications for A–D is our own deduction.

The cited regularity statements provide useful inputs to A, including an explicit triple-coalescence logarithm and estimates at every weighted derivative order. They do **not**, as stated, complete the effective exponential H¹ approximation theorem A or the construction/integration/linear-algebra obligations B–D. That conclusion is an audit of these statements, not a lower bound on what another method can achieve.

## Primary-source statements and exact scope

**Fournais, M. Hoffmann-Ostenhof, T. Hoffmann-Ostenhof, Sørensen: analytic structure.** [arXiv:0806.1004v1](https://arxiv.org/abs/0806.1004v1), submitted 5 June 2008; *Communications in Mathematical Physics* 289 (2009), 291–310, DOI [10.1007/s00220-008-0664-5](https://doi.org/10.1007/s00220-008-0664-5). Theorem 1.4, PDF p. 4, assumes a local H¹ weak eigenfunction. Near a collision of exactly one pair, with every other collision excluded, it gives ψ=a+|xᵢ|b or ψ=a+|xᵢ−xⱼ|b with a,b real analytic. The singular sets being excluded are defined on pp. 3–4. Remark 1.6 extends to molecules and general positive masses. Theorem 1.1, p. 2, treats a one-particle Coulomb singularity with analytic coefficients and forcing. These are local existence statements, with no numerical analytic radius or effective uniform constants supplied. They do not cover helium's simultaneous electron–electron–nucleus collision. Read: statements and definitions pp. 1–4, KS-transform setup and proof passages in §2. This is stronger than a cusp condition, but is not a global analytic factorization or an approximation algorithm.

**The same four authors: sharp regularity.** [arXiv:math-ph/0312060v1](https://arxiv.org/abs/math-ph/0312060v1), submitted 23 December 2003; *CMP* 255 (2005), 183–227, DOI [10.1007/s00220-004-1257-6](https://doi.org/10.1007/s00220-004-1257-6). For their −Δ kinetic convention, Theorem 1.1, PDF pp. 3–4, gives ψ=exp(F₂+F₃)φ₃ with φ₃∈C¹,¹_loc, including collision intersections. With yᵢ,A=xᵢ−R_A,

    F₂ = −½Σᵢ,A Z_A|yᵢ,A| + ¼Σᵢ<ⱼ |xᵢ−xⱼ|,
    F₃ = ((2−π)/(12π)) Σ_A Σᵢ<ⱼ Z_A(yᵢ,A·yⱼ,A)
                                log(|yᵢ,A|²+|yⱼ,A|²).

Theorem 1.4 and Remark 1.5, p. 6, give uniform-in-center local second-derivative estimates using cut-off factors. The uncut quotient need not remain L² at infinity (p. 5). The optimality argument on p. 5 excludes improving the remainder for **all eigenfunctions with one factor independent of eigenvalue and state**. It does not exclude a special ground-state representation. Read: pp. 1–8; §3.1 factor construction and §3.2 estimate setup. The lengthy auxiliary elliptic and angular calculations were not independently reproduced. No all-order factorial estimate is stated.

**Fournais–Sørensen: weighted derivative estimates.** [arXiv:1803.03495v1](https://arxiv.org/abs/1803.03495v1), submitted 9 March 2018. Theorem 1.1, PDF pp. 3–4, supplies local Lᵖ estimates for every nonzero multi-index α, with constants explicitly allowed to depend on α,N,Z,E,p and the ball radii. Put λ=min(1,dist(·,Σ)). Theorem 1.5, p. 5, gives

    ||λ^(|α|−a) ∂^αψ||₂ ≤ C_α ||ψ||H²,  a<5/2, |α|≥1,

for global H² eigenfunctions; its derivative-specific version uses a larger distance. Remark 1.4 distinguishes classical derivatives off Σ from global weak derivatives. The zero-order restriction yields weighted Sobolev membership at all orders for a<3/2 (pp. 6–7). Corollary 1.3 assumes exponential decay and transfers it to derivatives. Molecular extension is Remark 1.6(iii). Read: pp. 1–7, §2 rescaling and induction, §§3–4 result derivations. The induction does not state factorial control of C_α. Thus the displayed all-order theorem is not itself a weighted-analytic norm estimate. No journal DOI was verified from the arXiv metadata; the arXiv ID identifies the source used.

**Ming–Yu: recent quantitative Barron regularity, preprint only.** [arXiv:2608.22252v1](https://arxiv.org/abs/2608.22252v1), submitted 23 August 2026, *Sharp Barron Regularity Results for Coulombic Many-Electron Wave Functions*. For an H² eigenfunction on R³ᴺ, Theorem 1.1, PDF p. 3, states that both cut-off Jastrow quotients belong to Bˢ for s<2, where ||u||Bˢ=∫⟨ξ⟩ˢ|û(ξ)|dξ. It gives ||u||B²⁻ε≤Mε⁻²||u||B¹ and a B¹/H¹ estimate. M is computable and depends on N,E,charges,relative nuclear positions and the fixed cutoff profile. Equations (4.13)–(4.15), pp. 17–18, track its construction. Endpoint optimality is restricted to universal factors; part (iv) addresses bound states of the unperturbed two-electron atom. Read: §1, quantitative §4, §5 optimality proof, §6 theorem mechanism, §7 conclusions; no independent verification of every Fourier residue calculation. This new regularity theorem is not an exponential hp approximation, certified eigenvalue, or polynomial bit-cost theorem. No journal publication was verified.

**Morgan: Fock-series convergence requires a scope qualification.** *Convergence properties of Fock's expansion for S-state eigenfunctions of the helium atom*, *Theoretica Chimica Acta* 69 (1986), 181–223, DOI [10.1007/BF00526420](https://doi.org/10.1007/BF00526420). Only the primary publisher's abstract and metadata were accessible and read; the full proof is **not verified here**. The abstract distinguishes convergent Fock-series PDE solutions from proving that the physical decaying eigenfunction has such a representation. It constructs infinitely many series solutions for arbitrary, even complex, energy without the boundary condition at infinity, and discusses the physical-representation question separately. Consequently “Morgan proves convergence” alone cannot discharge A. This is a limitation of that citation, not a claim that the representation problem has remained open in every subsequent formulation. No theorem about A is inferred from this inaccessible full text.

Additional full-wavefunction successors, including corrected global blow-up regularity, Gaussian approximation, mixed derivatives and the 2025/26 Barron theorem, are audited in [hp_successors.md](helium_research/hp_successors.md). In particular, that audit distinguishes all-order weighted smoothness from quantitative analyticity and identifies the pair-edge restriction of the helium Green-operator expansion.

## Explicit deductions for the physical helium Hamiltonian

For the atom with its nucleus at the origin, write a point of R⁶ as (r₁,r₂). Its collision set is

    Σ = {r₁=0} ∪ {r₂=0} ∪ {r₁=r₂}.

These are three codimension-three linear subspaces, all intersecting at (0,0). Their distance is min(|r₁|,|r₂|,|r₁−r₂|/√2). Thus “isolated pair collision” means a point of one subspace different from the origin; the triple point cannot be covered by declaring another pair to be the singular pair. This is a direct check of the set definitions above.

The normalization must be converted before using numerical coefficients. If H_phys=−½Δ_r+V_R(r), let (Uψ)(x)=2^(−3N/2)ψ(x/2), with the nuclei of H_paper placed at 2R. U is unitary because dx=2^(3N)dr. Direct differentiation and Coulomb homogeneity give H_paper U=½ U H_phys. For helium, pulling the displayed factor back by x=2r therefore gives

    F₂,phys = −Z(|r₁|+|r₂|) + ½|r₁−r₂|,
    F₃,phys = ((2−π)/(3π)) Z(r₁·r₂)
                                     log(4(|r₁|²+|r₂|²)).

The log(4) contribution is an analytic quadratic and can be absorbed into the remainder. The powers and coefficients follow from substitution; no new regularity theorem is asserted. The spinless scalar statements apply componentwise to the finite spin decomposition, but identifying the scalar positive ground state with the physical antisymmetric singlet ground state requires the separate symmetry argument specified in the target.

H¹ is the relevant approximation norm for the target's form-based Ritz certificate. H² is the operator domain, a stronger requirement. For example, a continuous piecewise polynomial with a normal-derivative jump has a surface distribution in its distributional Laplacian; that term is not an L² function. Hence H¹ conforming approximation cannot silently justify an L² operator residual. Weighted classical derivatives outside a measure-zero singular set also cannot silently replace a global weak-derivative assertion.

## What remains to discharge A–D

| Obligation | Available input | Additional theorem needed |
|---|---|---|
| A: effective exp(−cp) H¹ approximation | Local pair analyticity, explicit triple singularity, weighted regularity, global Barron norm information | An explicit approximation estimate for the full stratified configuration space, with effective derivative growth, overlap/gluing constants and the tail at infinity; uniform nuclear-geometry dependence |
| B: polynomial basis size and construction | Explicit collision geometry and possible singular factors | A conforming mesh/enriched-space construction, count and parameter bit-size bound from nuclear data; functions depending on the unknown eigenstate cannot count as input data |
| C: certified matrices/conditioning | Explicit factors indicate which singular integrals arise | Norm-wise certified integration, Gram lower bounds, and sufficient working precision, each with polynomial bit cost |
| D: certified finite minimization | No new assertion from regularity alone | Validated lowest generalized eigenpair and near-optimal vector under the quantitative C bounds |

Compact noncollision nuclear geometry is useful, but compactness alone does not give computable constants or a specified bit complexity. An abstract local existence radius at each configuration is also not a covering with a proven polynomial count. For the unbounded domain, a decay exponent without a computable prefactor and H¹ tail estimate is insufficient to choose a certified truncation radius.

One constructive route worth pursuing is to rescale collision-free balls by λ=min(1,dist(·,Σ)). Coulomb coefficients on the scaled balls have controlled analytic derivatives for fixed dimension and bounded charges. A quantitative analytic elliptic estimate may then control derivative-order growth. This is a research route, **not a theorem proved by this audit**: the factorial constants, treatment of all intersecting strata, conforming approximation and certified quadrature must still be supplied. Triple logarithms do not themselves refute geometric refinement or singular enrichment.

## Audit trail and hand-waving avoided

The archived files use the unique prefix `regularity_` in [sources](helium_research/sources). Four complete primary PDFs and extracted page-numbered text files are retained. The cited theorem pages were rendered and visually checked; exact read scopes are given above. `regularity_archive_manifest.json` records URLs, versions, page counts and SHA-256 hashes. Reading selected proof passages is not advertised as independently checking every line of each paper.

The tempting shortcuts were: extend a pair theorem to the triple intersection; identify C¹,¹ with analyticity; identify all weighted orders with a factorial estimate; ignore the uncut factor at infinity; copy coefficients across different kinetic conventions; infer global weak derivatives from derivatives off Σ; and identify a convergent local/PDE series with the physical bound state. Each has instead been separated at the precise missing hypothesis. No empirical convergence fit is used.

The remaining theorem is the one already isolated by A–D: construct, for the promised unbounded two-electron Coulomb family, conforming spaces with effective uniform exponential H¹ approximation and polynomial dimension, together with certified polynomial-bit integration and lowest-eigenpair computation. The papers audited here neither prove nor refute that theorem.
