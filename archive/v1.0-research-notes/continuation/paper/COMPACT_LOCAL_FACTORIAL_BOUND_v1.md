> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Conditional compact assembly of factorial bounds, version 1

Let X be any topological space, K a compact subset, and J(k,x) an arbitrary family whose target at order k has a supplied norm. Suppose that every x in K has a neighborhood U_x and positive constants C_x,A_x such that, simultaneously for all y in U_x and all natural k,

\[
\|J(k,y)\|\le C_x A_x^k k!.
\]

There exist common C>=1 and A>=1 with this bound for all x in K and all k. The formal theorem proves the stronger conclusion on a single neighborhood of K. No continuity, derivative identity, analyticity, or PDE property of J is assumed or inferred.

The proof obtains a finite neighborhood subcover indexed by a finite subset s of K. It sets C=1+sum_{x in s} C_x and A=1+sum_{x in s} A_x. Positivity gives C_x<=C and A_x<=A for every selected index; monotonicity of natural powers and multiplication by the nonnegative factorial then gives the common bound. The union of the selected neighborhoods is a neighborhood of K, and every point of that union inherits one of the selected estimates. If K is empty, the chosen index type is empty, the finite sum constants are both one, and the bound is vacuous. No nonempty-set assumption is needed.

The generic target family may depend on k, allowing later instantiation by the spaces of continuous k-multilinear maps that contain iterated Fréchet derivatives. This flexibility adds no regularity assumption. The exact root `compact_factorial_bound_of_neighborhood_family` exposes the finite subset and explicit sum constants; `compact_local_factorial_bound_uniform_nhds` and `compact_local_factorial_bound_uniform` accept the local existential hypotheses.

This is a fully formal conditional compactness implication. In particular, the neighborhood factorial estimates remain explicit hypotheses and have not been derived from analytic or PDE assumptions within this unit. A separate analytic-function composition is required to discharge them for actual derivatives. The finite cover and local constants are selected noncomputably; no effective extraction procedure or bit-complexity assertion is supplied.

The two new modules have 13 declarations. They compile in the pinned Lean 4.34.0-rc2 environment and pass strict version-6 expanded-statement/axiom audits with only propext, Classical.choice and Quot.sound, and no printer failure. Existing pinned dependency objects were reused; this is not an isolated source rebuild. All earlier frozen and successful bytes remain unchanged.
