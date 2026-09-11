> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Root review of the two-center lower certificate

Reviewed exact sources:

- `../computation/box/TWO_CENTER_IMS_v1.md`, SHA-256 `c4b12cb838a89e4fc21748ae923c7e55cc1418185325a5094bc6bc87750fb6b6`.
- `../computation/box/two_center_ims_lower_v1.py`, SHA-256 `a0897a209a623290c6fcc088ecdc1b4a9bed98c27efd1e4840bf85f0c9507d01`.

This is a review of a paper continuum proof and exact rational program. It does not establish Lean verification of the molecular operator, IMS identity or implementation.

The weak H1 localization is valid even though the partition derivatives jump at the strip boundaries. Its squared gradients sum to theta'(t)^2/d^2 almost everywhere, and the kinetic coefficient 1/2 gives precisely the stated IMS subtraction. The translated hydrogen square completion applies to each localized spin component. The unlocalized opposite-center attraction is retained, then bounded using its axial distance lower bound. Both exterior half-spaces are included. This yields an actual form lower estimate, not a projected variational lower bound or a lower bound on only a finite matrix.

The parameter restriction forces monotonicity and the exact endpoint values of theta. Near each nucleus the opposite-center partition weight vanishes quadratically. The endpoint-cell inequalities therefore bound the removable ratios without dividing an interval by zero. A positive rational lower bound for the true half-distance increases every inverse-distance and gradient term, preserving the conservative direction. The symmetric closed-form example uses the correct identity [1-t sin(pi t/2)]/(1-t^2)<=1.

The implementation bounds whole cells. It uses monotonic endpoint weight bounds, respects the signed hydrogen coefficient, and uses unfavorable positive-denominator endpoints. The cosine interval routine includes its interior maximum at zero. The extra sine Taylor routine encloses the entire interval with a valid Lagrange remainder after the last retained odd term; it is not point sampling. Its intersections with the proved angle and sine ranges are legitimate. Every finite cell upper bound and both exterior constants enter the maximum, and negation is rounded outward for the energy lower endpoint.

The physical model and nucleus order are checked before combining with a previous stage. The CLI replays both the scalar lower certificate and the original molecular matrix certificate, and the strengthened checker repeats these computations and checks hashes. The optional internal no-stage-replay path is visibly tagged and is not the normal accepted checker path. Replaying the same implementation is disclosed; it is not an independent kernel proof.

No mathematical or rounding-direction error was found in the reviewed sources. Runtime/replay outcomes and concrete interval endpoints belong to the separately recorded execution receipts; they do not establish optimality of the partition family or arbitrary-precision convergence to the physical energy. The new result improves a valid lower endpoint for the same three-dimensional molecule and preserves the original upper trial space.

Historical origin: frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The prior molecular seal and all frozen artifacts remain unchanged.
