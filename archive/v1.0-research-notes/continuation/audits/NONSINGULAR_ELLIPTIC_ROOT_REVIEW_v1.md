> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent review of the nonsingular elliptic factorial estimate

Evidence: mathematical paper review, not Lean verification.

Reviewed `NONSINGULAR_ELLIPTIC_FACTORIAL_v1.md`, final SHA-256
`d776fd6de1ea4df30b5bbddfa0197d3d68c32b84514b9c5ccaaaebfb0d07feb0`.
The root read the complete proof, including its actual scaled Coulomb
application. The weak convolution license, cutoff energy estimate and
Young constants in E4 are valid. Two reserved H2 gains give every mixed
derivative through order four, with the stated E5/E6 coefficient counts.
The maximal norm accounts for the commutator derivative allocations,
including low-order edge cases, and the bounded potential loses an order
without a smallness assumption. The recurrence coefficient B0=2CA
dominates the combined terms; the geometric induction and tensor-product
pointwise estimate give exactly the displayed factorial constants.

The physical scaling retains the factor two from the kinetic operator
-Delta/2 and the epsilon-squared energy term. The normalized difference
equation and the return to an epsilon-sized original difference have the
correct signs and factors. No correction was requested in this review.

The result is an actual weak-solution quantitative local estimate,
conditional on the stated analytic coefficient/source bounds. Its
physical application still requires the actual solution and regularity
inputs; those are not obtained by proving this operator lemma. The finite
diagnostics supplement the paper proof and do not verify its infinite
analytic assertions. Frozen provenance and precise local dependencies
are recorded in the reviewed artifact.
