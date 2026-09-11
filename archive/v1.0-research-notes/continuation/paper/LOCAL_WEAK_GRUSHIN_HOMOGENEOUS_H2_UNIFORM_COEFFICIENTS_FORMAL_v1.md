> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local weak H² uniform over bounded potential families

Evidence category: fully formalized continuum theorem. For any finite spectator set κ, c>0, open Ω⊂R⁴×R^κ and real C∞ compact cutoff χ supported in Ω, the theorem first chooses a compact K⊂Ω containing supp χ and a function C: R×R→[0,∞). These choices precede both B and G.

For every real B∈C∞(Ω), numerical β,β1 satisfying |B|≤β and Σ_j|D_tj B|²≤β1² on K, and every raw complex G∈L²_loc(Ω) satisfying the actual compact-test equation

    (−Δ_Y−c|Y|²Δ_T+B)G=0,

the result constructs U=χG almost everywhere and actual global L² first weak derivatives a(v) and all ordered second weak derivatives b(v,w), for every constant product direction v,w. With standard product orthonormal coordinates,

    ||U||² + Σ_i||a(e_i)||² + Σ_iΣ_j||b(e_i,e_j)||²
       ≤ C(β,β1) ∫_K |G|².

No first derivative, H², or differentiated-equation premise is imposed on G. Local square-integrability is genuine restricted L² membership on every compact subset of Ω. The weak equation is tested against every real C∞ compact test supported in Ω; integrability is supplied by the existing local reduction lemmas.

The common integration region is the union of the first-gain region for an outer plateau ρ and the second-gain region inside the plateau. Both are chosen using geometry alone. The same β,β1 bounds restrict to both regions, and monotonicity of the local square integral transfers the first-gain estimates to their union.

The arithmetic constructor `homogeneousH2Coefficient` is explicit. Let m=4+card κ, and let Cθ,Mχ,Aχ,Dχ be the second-gain and inner-cutoff bounds, all selected before B. Let Mρ,Aρ,Lρ,Eη,Rη be the fixed first-cutoff/energy-cutoff bounds. Define

    Q(β,β1)=Mχ²+2(Mχ²+mAχ²)
      +3m[Mχ²(1+Cθ/(16c)(2β1²+1+2β²))+4Aχ²+mDχ²],
    J(β)=4Aρ²+16Lρ(Eη²/2+Rη)+(2Mρ²+8LρEη²)β²,
    C(β,β1)=Q(β,β1)[3Mρ²+(9/4)J(β)+J(β)/(16c)].

The constructor is proved nonnegative for c>0, Cθ,Lρ,Rη,m≥0. All remaining real parameters enter squares. The final proof uses precisely this constructor. A family Bε satisfying the same numerical bounds on the common K therefore has the same H² constant. The theorem does not infer those bounds for any physical scaled family; that is a separate application obligation.

This completes the coefficient-family quantifier strengthening left open in `LOCAL_WEAK_GRUSHIN_HOMOGENEOUS_H2_QUANTITATIVE_FORMAL_v1.md`. It preserves that earlier fixed-potential theorem and its checkpoint unchanged. The earlier selected-jet second-gain theorem remains an explicit intermediate implication; its derivative witnesses are actually constructed here by the first gain.

The two new modules, three declarations, and their expanded statement/axiom audits passed using the reviewed v5 tool. Only propext, Classical.choice and Quot.sound occur. Pinned library and prior continuation objects were reused. No new isolated source rebuild was attempted; these modules lie outside the earlier 671-target snapshot.

The cutoff and gain constants are finite analytic existence data. Their selection is not an executable algorithm, and this result does not yet express every geometric constant in the H12 box-gap parameters. The coefficient is uniform over B and G at fixed c,κ,Ω,χ; no uniformity as c→0 or system size grows is asserted. The real C∞ coefficient hypothesis is stronger than the paper's finite C¹¹ hypothesis and is appropriate for the intended analytic-potential application.

The next consumed obligation is the actual inhomogeneous finite derivative bootstrap and Y-elliptic recovery for H¹², with coefficient/source derivative reserves stated explicitly. Twelve derivatives do not imply the all-order factorial estimate. No factorial, global dictionary approximation, spectral, numerical, bit-complexity or full Theorem T conclusion is asserted here.
