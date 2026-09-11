> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Common weak radial graph coefficient

For actual compact weak H2 f with true output Pc f=h and support K in one Y-coordinate slab of half-width R>0, c>0 gives the common explicit coefficient C=4R²+2R+2+2/c. The squared L2 norm of f, every first Y or T derivative, every YY derivative, every |y|-weighted YT derivative, and every |y|²-weighted TT derivative is at most C²||h||². Existing energy, exact-radius Poincare, radial maximal estimates, and scalar inequalities discharge all bounds. No smoothness of f or bound on approximant support radius is assumed. This is the compact order-two graph step toward the fixed outer norm, not an all-order or factorial theorem.

The single theorem compiles under Lean4.34.0-rc2; strict v7 checks its complete expanded statement and standard-only axiom report. Pinned library objects were reused; no isolated source rebuild.
