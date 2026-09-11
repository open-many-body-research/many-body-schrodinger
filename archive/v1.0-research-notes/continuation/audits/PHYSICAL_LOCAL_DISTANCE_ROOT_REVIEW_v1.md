> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Root review of the local physical distance theorem

Reviewed source: `PHYSICAL_LOCAL_DISTANCE_ANALYTIC_v1.md`, SHA-256
`8e65d5d7053012e7b40d891f9a310794aa446f87dde902770a9c13ffe4635f3e`.
Evidence: paper theorem with explicit physical solution premises, independently reviewed; no Lean assertion.

I checked the interfaces to the previously reviewed weak KS, H12 initialization, factorial recurrence, coefficient descent, nonsingular elliptic estimates and boundary-germ theorem. The seven-variable Taylor radius has sum-norm factor at most 1/4. The descent has three spectator variables, so its half-polydisc bound is exactly 16M and 16DM; it is not a bound obtained by ignoring coordinate multiplicities. The vertex estimate 16M(1+delta D) is at most 17M using delta D<=1/48. SO(2) invariance of the two separate coefficients follows from the proved uniqueness of analytic-plus-radius decomposition. Electron exchange is applied to the exchanged function and is not an assumed symmetry.

The cover is quantitative. Distance to each vertex of the perimetric simplex equals the corresponding physical collision separation. Transferring a smallest perimetric coordinate to another coordinate moves the point by exactly that minimum and reduces any separation by at most twice it. On the remaining interior, Heron's formula gives w>=4gamma^3. The retained Cartesian margins dominate every inverse-coordinate denominator and positive-square-root restriction in the boundary lemma. The radius for a complex germ is reduced again before recentering, leaving the claimed common margin.

Compatibility uses agreement on a full-dimensional real physical neighborhood, not only on the two-dimensional normalized shell. Convex equal-radius overlap supplies a real center and an adjacent positive-octant open set in each overlap. This is sufficient for holomorphic uniqueness. The bound h<=1/12 and the scale bound keep these real neighborhoods inside the original physical ball.

The proof explicitly distinguishes the organizing sum a+b+c from the frozen physical weight r+s=a+b+2c. The original fitting shell is contained in the perimetric shell [1/8,2], giving radius h/8. The final weighted derivative estimate treats order zero separately and uses S_phys/2<=S_per<=S_phys at positive orders. The original dictionary and physical weight are therefore retained.

No remaining error was found in the reviewed composition. Its conclusion is local G1 for an actual Lipschitz, rotationally invariant weak solution. Existence of the physical ground branch, its regularity and symmetry, exterior decay, and all formal analytic obligations remain separate. This result cannot yet be substituted into full Theorem T without those proofs.

Historical origin: frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`; source path/hash provenance is explicit in the reviewed theorem. All successful prior artifacts remain unchanged.
