> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Quantitative local weak H² for a fixed smooth potential

Evidence category: fully formalized mathematical result, with the fixed-potential scope stated below. This is a local continuum theorem and is not an algorithm or a factorial analytic estimate.

Let κ be any finite spectator index set, c>0, and Ω open in R⁴×R^κ. For a fixed real C∞ potential B on Ω and a real C∞ compact cutoff χ supported in Ω, there are compact K⊂Ω containing supp χ and C≥0, chosen before G, such that every raw locally L² complex G satisfying the actual compact-test equation (−Δ_Y−c|Y|²Δ_T+B)G=0 admits U=χG almost everywhere and genuine global L² first and all ordered second weak derivatives, with

    productCoordinateH2Sq(U,a,b) ≤ C ∫_K |G|².

No derivative or H² premise is imposed on raw G. The norm is the squared L² norm plus sums over the standard product orthonormal coordinate directions of all first and ordered second derivative squared norms. It therefore includes the mixed directions.

The first gain constructs Y, T and ordered YY jets. Differentiating the actual equation only in a spectator direction produces forcing −(D_T B)G. A shared outer cutoff gain and the finite-family forcing bound construct e_TT with

    Σ ||e_TT,j||² ≤ Cθ/(16c) [2 β1² ||G||² + (1+2 β²) Σ ||d_T,j||²],

where |B|≤β and Σ|D_T,j B|²≤β1² on its common compact region. No spectator-count factor was inserted in this aggregate forcing estimate.

For inner cutoff bounds |χ|≤M, |D_iχ|≤A, |D_i²χ|≤D and m=4+card κ, the second-gain coefficient is

    Q = M² + 2(M²+m A²)
        + 3m [M²(1+Cθ/(16c)(2β1²+1+2β²)) + 4A² + m D²].

It multiplies ||G||²+Σ||d_Y||²+Σ||d_T||²+Σ||e_YY,ii||². Nested weak localization and the full product Laplacian converse construct the compatible complete weak derivative family.

For the outer first cutoff ρ and its energy plateau η, use bounds Mρ,Aρ,Lρ,Eη,Rη from the actual cutoff functions. Set

    J(β) = 4Aρ²+16Lρ(Eη²/2+Rη)+(2Mρ²+8LρEη²)β²,
    S(β) = 3Mρ²+(9/4)J(β)+J(β)/(16c).

The final proof uses C=Q S(β). All selected constants are finite analytic existence data; their selection is noncomputable and no procedure for evaluating them is asserted.

**Quantifier limitation.** The final v1 raw-data theorem fixes B before choosing K,C. It is uniform in raw solutions, but does not by itself give a common constant for a family Bε. A separate compiled and audited intermediate theorem, `local_weak_grushin_second_gain_uniform_coefficients`, chooses K,Cθ,M,A,D before B and exposes Q(β,β1); it still requires the actual first-gain jets. The final coefficient-family-uniform raw-data composition remains the next obligation at this checkpoint.

All six new units and eight declarations in the accompanying checkpoint compiled using pinned library and continuation object caches. Expanded statements and axiom dependencies passed strict audit; only propext, Classical.choice and Quot.sound occur. Sources and objects match their receipts. No new isolated source rebuild was run; these units are outside the earlier 671-target rebuild snapshot. The v3 comment-scanner false-positive audit is preserved; the reviewed v5 auditor checks the unchanged passed source correctly.

No claim is made here about factorial constants, collision-scale uniformity for the final raw-data theorem, global dictionary approximation, spectral certification, novelty, bit complexity, or full Theorem T.
