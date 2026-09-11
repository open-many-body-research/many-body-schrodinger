> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Smooth cutoff rescaling with explicit derivative factors

For a supplied smooth compactly supported real function η on a finite-dimensional real normed space E, define the actual translated, rescaled function

\[
\eta_{a,r}(x)=\eta\bigl(r^{-1}(x-a)\bigr).
\]

For nonzero r, the affine map is proved to be a homeomorphism with inverse y↦a+ry. The formalization proves C∞ regularity and compact support, and the exact topological support identity

\[
\operatorname{tsupp}\eta_{a,r}
=a+r\operatorname{tsupp}\eta.
\]

Any plateau where η=1 transports by the same affine image. For r>0, open and closed balls about zero with radius R transport exactly to the corresponding balls about a with radius rR. Consequently a base cutoff supported in the closed ball of radius Rout and equal to one on the closed ball of radius Rin retains these properties at radii rRout and rRin. These are exact identities in the norm specified on E.

The first and ordered second derivative chain rules are proved explicitly:

\[
D_v\eta_{a,r}(x)=r^{-1}D_v\eta(r^{-1}(x-a)),
\]
\[
D_wD_v\eta_{a,r}(x)=r^{-2}D_wD_v\eta(r^{-1}(x-a)).
\]

The operator-norm hypotheses are genuine Fréchet derivative bounds

\[
\|D\eta(x)\|\le L_1,\qquad \|D(D\eta)(x)\|\le L_2.
\]

For positive r, the formal conclusions are

\[
|D_v\eta_{a,r}(x)|\le(L_1/r)\|v\|,
\qquad
|D_wD_v\eta_{a,r}(x)|\le(L_2/r^2)\|v\|\|w\|.
\]

A supplied value bound |η|≤M is preserved. The final package returns smoothness, compact support, the support and plateau ball properties, the value bound, and both derivative bounds for this same concrete rescaled function.

The derivative arguments work in any real normed vector space; the packaged geometry is stated for the requested finite-dimensional class. Applying the theorem to an ordinary Cartesian product uses its maximum norm and operator norms induced by that norm. Applying it to the `WithLp 2` Euclidean copy uses that Euclidean norm. Neither the statement nor proof identifies these distinct norms. Pure factor directions can be normalized separately when a downstream argument requires unit directions.

The base cutoff, its support/plateau radii, and its actual derivative bounds remain explicit supplied data. This checkpoint does not claim to construct a particular numerically certified base cutoff or to compute L1,L2. It proves how those data transform under translation and scale, which is the needed coefficient step for uniform localization estimates.

Sources: `SmoothCutoffRescaleGeometry_v1`, `SmoothCutoffRescaleBalls_v1`, `SmoothCutoffRescaleDerivatives_v1`, and `SmoothCutoffRescaleQuantitative_v1`. Exact hashes and strict expanded-statement/axiom receipts are recorded in `audits/SMOOTH_CUTOFF_RESCALING_CHECKPOINT_v1.json`. Standard foundational axioms only. Pinned library and project development objects were reused; these modules postdate the completed v18 isolated source rebuild.

No factorial estimate, analyticity theorem, approximation rate, executable solver, or full Theorem T is claimed. Frozen artifacts remain unchanged: original `RWA_REPORT.md` SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, freeze `THEOREM_T_FREEZE_2026-09-09_212604`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.
