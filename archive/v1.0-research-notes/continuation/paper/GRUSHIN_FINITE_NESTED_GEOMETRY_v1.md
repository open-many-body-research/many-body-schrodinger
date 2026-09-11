> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Arbitrary finite nested cutoff geometry, version 1

For any center in the actual Grushin space R^4 times R^3, any positive inner half-widths bY,bT strictly smaller than outer half-widths aY,aT, and any finite stage count n, the formal construction supplies n actual smooth cutoff stages. The geometry is fixed from these data before any solution or PDE is specified.

The gap is delta=min(aY-bY,aT-bT)/(2(n+1)). At stage k the open region has half-widths aY-2k delta and aT-2k delta. The middle region consumes one additional gap; the next outer region consumes two. The cutoffs are the existing actual h12InnerCutoff and h12EnergyCutoff, with their proved support, plateau, and first/second derivative bounds.

The exact scalar margin identity is 2(n+1)delta=min(aY-bY,aT-bT). Consequently the terminal half-widths are strictly larger than bY,bT: an unused collar of at least two gaps remains. The requested closed inner box is contained in the final open region. Every region is open and measurable, the region sequence is antitone, and all regions are contained in the initial open box.

The geometry theorem permits a nonnegative coefficient c(k) at each stage. Its quantitative constants are M=D=1, S=norm(centerY)+2aY, A(k)=(4+3c(k)S^2)*8*(C2+C1^2)/delta^2, and B(k)=Q(k)=(4+3c(k)S^2)*(4C1/delta)^2. C1 and C2 explicitly bound the derivatives of the actual C-infinity Real.smoothTransition. The theorem assumes no uniform bound depending on a solution and no regularity or PDE conclusion. Setting n=2m and using c for the first m stages and zero for the next m supplies the requested geometric input to spectator then spatial finite recovery. The PDE coefficient is not determined by the zero used in the spatial cutoff estimates.

The principal API is `finite_grushin_nested_geometry`, with `finite_grushin_nested_final_contains` and `finite_grushin_nested_domains`. The underlying `finite_grushin_step_geometry` accepts any positive gap satisfying 2n delta<=aY,aT. Region and cutoff arrays are `finiteGrushinRegion`, `finiteGrushinMiddle`, `finiteGrushinInnerCutoff`, and `finiteGrushinEnergyCutoff`.

Three new modules and 25 exact declarations passed the pinned Lean 4.34.0-rc2 environment and strict expanded-statement/axiom audits. Only propext, Classical.choice and Quot.sound occur. No printer failure was found in either strict log. Existing dependency objects were reused; no isolated source rebuild was attempted for this unit. All older frozen and successful artifacts remain unchanged.

This is a finite geometry prerequisite for the R02 local regularity composition. It does not itself prove a PDE regularity estimate, an all-order analytic bound, a factorial rate, a global approximation theorem, Theorem T, or an executable certified energy solver. The displayed dependence on n is a formula for geometric constants, not a bit-complexity claim.
