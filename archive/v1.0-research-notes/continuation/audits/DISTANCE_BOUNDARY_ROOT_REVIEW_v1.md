> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent review of distance charts and boundary gluing

Evidence: paper review, not Lean verification.

Reviewed final `DISTANCE_BOUNDARY_GERMS_v1.md`, SHA-256
`b956af4f732085ae83eb9ace3a965a59ca18bd85e922178f3453f58748c86991`.
The root independently read all eight sections, including the explicit
coordinate estimates. The nuclear, pair, collinear and noncollinear
constants are conservative; all square-root denominators are used only
where the chosen analytic branch is bounded away from its singularity.
The SO(2) series proof supplies an analytic invariant function before
evaluating a square root, so it does not assume an invalid analytic
inverse of the distance map at a collinear point.

The gluing proof uses real centers and full real open physical octant
agreement, including radial neighborhoods. Its radius-weighted point lies
inside each overlap and in the closed physical octant. A full-dimensional
open agreement set then licenses the holomorphic identity theorem. The
normalized two-dimensional simplex is used only for centers; agreement on
that simplex alone would not suffice. The finite-cover recentering and
distance-to-perimetric radius conversion retain the asserted margins.

Review requested that the abstract SO(2) statement explicitly specify real
spectator centers. Otherwise its real-domain invariance assumption could
be vacuous on an off-real polydisc. The final source makes this scope
restriction explicit; all intended physical applications already have
real centers.

The accepted output remains conditional on the stated Cartesian analytic
data, physical rotational invariance and actual solution. It proves
compatible distance/perimetric analytic germs with quantitative bounds,
not those physical premises, the full global approximation theorem, or
Theorem T. Frozen provenance and the quantitative KS dependency are
specified by hash in the reviewed artifact.
