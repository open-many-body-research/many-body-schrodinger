> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Focused finite Y iteration review

Reviewed final sources and complete expanded statements for MixedYIterationBudgetSequence_v1, MixedYFiniteIteration_v1, MixedYFiveStepReserve_v1 and MixedYIterationBudgetScale_v1. Strict receipt formal_semantics/20260910T212841_339355Z covers twelve declarations with standard axioms only, no source-forbidden tokens, no ellipses, and immutable source/object hashes.

Checks attempted:

- The finite iteration hypothesis contains only the original raw weak PDE and an initial genuine triangular state. There is no assumed differentiated PDE, gain map, derivative norm conclusion, or future regularity.
- At every stage the prior actual state is used, r advances by exactly two, m is unchanged, and the same f is retained. Source budgets, source weak links, smooth coefficients, coefficient bounds and the original PDE are restricted along proved domain inclusions. Weak links are restricted by test support, not by multiplying unknown derivatives.
- The cutoff geometry uses principal coefficient zero for Y-Laplacian recovery while the original PDE keeps arbitrary c. The theorem does not replace the physical equation with c=0.
- Five stages from r=2,m=12 conclude r=12,m=12. Source and coefficient orders are exactly total≤10, with weak source edges strictly below ten. Source T links on pure T words suffice because the single-stage theorem proves the mixed commutations. No input higher Y solution derivatives occur.
- Output is the supplied Omega5. Twelve earlier spectator stages consume 24 gaps only when instantiated with the actual two-gap schedule; the five Y stages then consume ten further gaps. This arithmetic is not substituted for physical geometric containment in the generic theorem.
- Per-word bounds are not relabeled as sums over all multiindices. Higher output norm assembly is separately owned.
- Budget positivity follows from max retaining the previous budget. Monotonicity uses finite-stage L,D,Q≥0. Common-factor homogeneity requires r≥0, explicitly accounting for max; the proof makes no division by r.

No concrete defect was found. Development failures were Lean layout/definitional unfolding and arithmetic index alignment, plus one prematurely attempted dependent build before its budget module existed. Those logs are preserved; final exact sources compile and strict-audit cleanly. No new isolated source rebuild was run; pinned dependencies were reused.
