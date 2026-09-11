> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual interval point evaluation via FTC and L2

For real a<b, a normed real codomain F, g,dg continuous on [a,b], and genuine HasDerivAt g (dg t) t at every t in [a,b], the modules prove at every x in [a,b]:

norm(g x) <= (b-a)^(-1) integral_[a,b] norm(g) + integral_[a,b] norm(dg),

and

norm(g x) <= (sqrt(b-a))^(-1) sqrt(integral_[a,b] norm(g)^2) + sqrt(b-a) sqrt(integral_[a,b] norm(dg)^2).

The first follows from the actual two-point FTC norm bound and integration in the second point. The second follows from actual L2 Cauchy-Schwarz with the constant-one field. There is no derivative order or function-dependent constant. The same first inequality is expressed using the normalized interval measure mu=(ofReal(b-a))^(-1) smul volume.restrict(Icc a b): enorm(g x) <= integral enorm(g) dmu + ofReal(b-a)*integral enorm(dg) dmu. The normalized measure has mass one. No interval pointwise bound is assumed.

The derivative field is actual by HasDerivAt, not an arbitrary list of budgets. Both endpoints are included; a=b is only permitted in the preceding undivided two-point/length-multiplied statements. The code does not assume a complete codomain for the norm bounds. Continuity supplies the actual restricted integrability needed for Cauchy-Schwarz.

All 9 declarations in IntervalPointwiseFTC_v1, IntervalPointwiseL2_v1 and IntervalPointwiseAverage_v1 compiled and passed approved v7 exact-statement/axiom audit formal_semantics/20260910T235558_526378Z. Expanded types and full axiom reports were read. Only propext, Classical.choice, Quot.sound occur; no forbidden source tokens, printer ellipses, failure or omission diagnostics. Source and objects remained unchanged.

Independent read-only reviewer /root/finite_affine_jets/physical_direction_norm matched all three exact source hashes and found no hypothesis, endpoint, scaling or square-root defect. The reviewer read the actual FTC restriction and norm symmetry, integrated length factor, constant-one L2 Cauchy estimate, positive-length square-root cancellation and normalized-measure ENNReal cancellation. No compiler/auditor was run by the reviewer.

These are the one-dimensional mathematical prerequisites for R24, not the full seven-dimensional embedding or its weak representative extension. Tensor integration, rectangular geometric normalization and weak density remain separately stated work. No solution regularity, evaluated all-order PDE constant or original T02 verification is claimed. Pinned cached dependency objects were reused; no source rebuild or broad audit was performed. All prior PASS/frozen artifacts and shared ledgers were preserved.

Historical context: rwa_proof/THEOREM_T_COMPOSITION.md, SHA-256 1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da, frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09, inventory THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json.
