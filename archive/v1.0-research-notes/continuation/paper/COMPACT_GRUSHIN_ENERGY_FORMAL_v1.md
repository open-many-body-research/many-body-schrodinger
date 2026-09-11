> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact smooth Grushin energy and Cauchy estimates

Let Y and T be arbitrary finite-dimensional Euclidean coordinate spaces, with their actual product Lebesgue measure, and let P_c=-Delta_Y-c|y|^2 Delta_T. For every complex-valued smooth compactly supported G and every real c, the formal theorem proves

    E_c(G) = integral real-inner(G,P_c G),
    |E_c(G)| <= sqrt(integral |G|^2) sqrt(integral |P_c G|^2),
    E_c(G)^2 <= (integral |G|^2)(integral |P_c G|^2),

where E_c is the existing sum of squared Y-derivative integrals plus c times the |y|^2-weighted squared T-derivative integrals. The proof constructs a smooth compact cutoff equal to one near the entire support of G, proves its derivative error multiplied by G vanishes pointwise, and specializes the already proved compact-cutoff energy identity. Actual L2 membership of both G and P_c G is derived from compact support and smoothness.

For c>=0, E_c is nonnegative and dominates the sum of squared Y-derivative integrals. That Y sum squared also obeys the same Cauchy product bound. No Poincare or output-norm estimate is assumed. The separate slab Poincare result may now combine with these estimates to control G and its first Y derivatives by P_c G.

Evidence: both exact modules compile in Lean4.34.0-rc2; a joint v7 strict expanded-statement and axiom audit passes all six declarations with only standard foundational axioms, no printer failures or ellipses, and unchanged source/object hashes. An independent agent reviewed the exact sources and direct energy/plateau/operator/L2-Cauchy dependencies without finding an error. Existing pinned dependency objects were reused; this unit is not an isolated source rebuild.

The first energy development attempts failed at narrow simplifier/elaboration steps (constant-derivative lemma name, an overbroad reverse rewrite, then lambda application rewriting); the final proof uses direct pointwise congruence. All failed logs are preserved. No mathematical statement was weakened or inherited mathematical error found. This completes a compact smooth energy prerequisite on the reduced R02 path; it is not a proof of the entire all-order approximation theorem or full Theorem T.
