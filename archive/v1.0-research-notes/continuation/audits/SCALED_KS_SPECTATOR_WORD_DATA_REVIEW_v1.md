> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Focused review: scaled KS spectator word data

Reviewed the four final sources and complete expanded statements in formal_semantics/20260910T210603_214108Z. Exact axiom reports cover ten declarations, with no forbidden source tokens or printer ellipses; all source/object hashes remained unchanged.

Checks attempted:

- Derivative order: recursive cons is the outer derivative. Fin.cons enters the first slot in iteratedFDeriv_succ_apply_left', matching the recursive definition without permuting derivatives.
- Locality: the induction uses equality throughout the open coefficient patch to obtain eventual equality at the differentiation point. It does not differentiate an equality known only on the compact subset.
- Norm: every actual product spectator basis vector has norm one in the maximum product norm. Multilinear operator norm gives a product of ones, not an omitted dimension factor.
- Source identity/sign: F_w is explicitly D_w b smul (-a0). It is the bare b source, while the operator coefficient is epsilon b. The amplitude sign is preserved; only norm_neg simplifies the integral bound.
- Integrability: local source L² comes from actual smooth coefficients and a constant complex amplitude. Region L² comes from a measurable bounded function on a finite measure restriction. In the physical wrapper finite measure follows from S subset compact K; it is not inferred from ENNReal.toReal alone.
- Uniformity: M depends on the fixed compact patch, charge, energy and finite reserve. It precedes epsilon, word, amplitude and region. No uniform dependence on reserve m is claimed.
- Inputs: no unknown solution or solution derivative occurs. The physical coordinate subtype is retained.

No mathematical defect was found in these checks. One development compile failed only because simp did not discharge a finite natural order below the smoothness index; replacing it with the exact ENat coercion inequality fixed compilation. The failed development receipt is retained. Final proof bytes are sealed. Verification reused pinned dependency objects; this is not a new isolated source rebuild.
