> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Focused adversarial review of the local elliptic H² chain

Reviewed 2026-09-10. **No mathematical or statement-level defect was found in
the reviewed local elliptic chain.** This is a source and evidence review of
existing compiled proofs, not a new proof, recompilation, isolated rebuild,
independent implementation, or novelty determination.

The exact established result is the cutoff criterion for local weak H²: on an
open set in any finite-dimensional real Euclidean space, complex functions
`f,w` that are locally L² and satisfy the actual Laplacian identity against
every real smooth compact test have genuine global weak first and ordered
second L² derivatives after multiplication by every smooth compact cutoff
supported in the open set. The product result uses the actual sum of squared
factor-coordinate derivatives, the ordinary Cartesian product, and product
Lebesgue measure. It returns one first-derivative family for each cutoff and
an L² witness for every ordered second direction pair.

The reviewer read the exact nine target sources below, their definitions and
relevant expanded theorem statements, the complete axiom reports, and the
seven supporting sources listed later. Current target source and object hashes
were checked against their strict audit receipts; audit-source and full
expanded-log hashes were also rechecked. The nine target modules contain 27
audited declarations. All six receipts report successful compilation, no
printer ellipsis, complete axiom reports, no forbidden source tokens, and only
`propext`, `Classical.choice`, and `Quot.sound`. No source was edited or
recompiled during this review.

| Attempted failure | Exact check and result |
|---|---|
| Circular first-derivative premise | The final local theorems assume local L² data and the compact-test equation only. `generic_local_elliptic_first_gain` constructs `U=χf`, `A=χw−(Δχ)f`, `Bᵢ=2(Dᵢχ)f`; it derives first derivatives from `ΔU=A+ΣDᵢBᵢ`. The later multiplier helper has an explicit H¹ premise, but `generic_nested_cutoff_h2` supplies it from this preceding proof. |
| Wrong negative Sobolev index or Fourier normalization | Mathlib's `MemSobolev` is the actual Bessel-potential condition on tempered distributions. An L² input lies in order zero, hence order −1. Each derivative of an L² `Bᵢ` lies in order −1. The proved identity `J²u=u−(2π)⁻²Δu` and Bessel composition raise order −1 to +1. There is no −1-to-2 jump. The second gain uses an actual L² Laplacian. |
| Incorrect cutoff commutator sign | Testing the equation with `χφ` gives `Δ(χf)=χw−(Δχ)f+ΣDᵢ(2(Dᵢχ)f)`. Expanding the divergence recovers `χw+(Δχ)f+2Σ(Dᵢχ)Dᵢf` when the derivatives exist. The source signs and factor two agree. |
| Hidden global integrability or vacuous total Bochner integrals | The localized proof constructs genuine L² indicator extensions on the measurable closed set `tsupport χ`. Multipliers and test Laplacians vanish outside their proved supports. Products and finite sums used in integral algebra are proved integrable from L² and bounded compact smooth tests. Arbitrary behavior of `f,w` outside the relevant support is never differentiated. |
| Boundary distribution from the indicator extension | The proof does not assert that the derivative of the indicator extension equals an indicator times a derivative. It uses that extension only inside products/tests supported in `tsupport χ`, and derives the localized equation by testing `χφ`. Thus no boundary derivative is silently discarded. |
| Insufficient plateau hypothesis | `η=1` on `tsupport χ` suffices because the coefficients `2Dᵢχ` have support inside that set. This gives `Bᵢ=(2Dᵢχ)F` for the already derived H¹ function `F=ηf`, without differentiating the identity `F=f` at the support boundary. Smooth compact coefficient bounds and their first directional bounds are constructed. |
| Assumed outer cutoff or unjustified support enlargement | The final open-set theorem constructs the outer plateau cutoff by a finite smooth bump cover of the compact `tsupport χ`. Its entire support remains in the prescribed open set. Local L² on that larger compact support follows from the stated compactwise data hypothesis. |
| Nonstandard local L² definition | `GenericLocallyL2On` means L² on every compact subset of the open set. The separate neighborhood equivalence proves both directions using compact induction, finite union measure domination, and compact closed-ball neighborhoods. It does not require a global L² representative of `f`. |
| Max-norm product mistaken for a Euclidean space | The product proof explicitly moves to `WithLp 2 (Y×T)` via a linear homeomorphism. Local L² uses the exact restricted-measure transport on images of compact sets. Compact supports and the open domain move by the actual homeomorphism, and the factor-coordinate Laplacian is identified with the Euclidean-copy Laplacian by actual second-derivative chain rules. The output then returns by the L² unlift isometry and compact-test weak-derivative transport. |
| Weak H² output defined as an assumption or a surrogate | `HasWeakL2Order` recursively supplies actual `Lp ℂ 2 volume` derivative witnesses tested against every real smooth compact function. `ProductLocalWeakH2On` displays these same genuine product tests explicitly. No finite basis projection replaces the unknown and no derivative witness appears among final input hypotheses. |

The result is qualitative. It gives no bound uniform in a regularization
parameter, no quantitative local H² estimate, no analytic or factorial bound,
and no executable derivative-selection procedure. Its local derivative
witnesses are supplied separately for each cutoff; a single chosen global
derivative field on the whole open set is not the displayed output. It cannot
be applied directly to a weak Grushin equation merely from `P_c f∈L²`:
the required full factor-Laplacian equation with L² right-hand side must first
be proved for the actual partially regularized input. No such unresolved step
is assumed or discharged by these local elliptic modules. Full Theorem T is
unaffected by this review.

Target source fingerprints (all paths relative to `lean/`):

| Source | SHA-256 |
|---|---|
| `GenericNegativeSobolevGain_v1.lean` | `fba4c8ae54b0a4ed6ed232a45927f5c3bbf485868a8569d498abec8a4df04154` |
| `GenericLocalCutoffLaplacianTests_v1.lean` | `6b2e08bab5ca06e3ef951341e2326948f0e404e9034925c586be8d82337adc39` |
| `GenericLocalEllipticFirstGain_v1.lean` | `b5d569cebbb0547312b00b5d6e2498e4863d85fbb8dd62f7bac69b62ca217e38` |
| `GenericH1MultiplierDivergenceGain_v1.lean` | `f768950ea571c4d357a72c856ec70c8046bea44c680ddb14d0d7bf004827d2a2` |
| `GenericNestedCutoffH2_v1.lean` | `dbfdff90e1ad1b3f76bdec5777d875dbfc0d8597f486e5c88e44de2440d1bf98` |
| `GenericLocalEllipticH2_v1.lean` | `07cfb86c06cd13396aa14d1ae3928bbbe912fb220df37845fe0885a0ed96504a` |
| `GenericLocalL2Neighborhoods_v1.lean` | `fc4a362eb713ac8002e4f9fe25603c11262f94123024d20e536e2eaef118ce7e` |
| `ProductLocalEllipticTransport_v1.lean` | `f4f8507d61422835f1775f34cf14f54aba1ebaf84456397473e01e8a232067af` |
| `ProductLocalEllipticH2_v1.lean` | `006067e3219a6a770112ef98a8c3247a883483ed22ba91ab7eac402f19d15ba8` |

Strict receipts, relative to `audits/formal_semantics/`:

| Receipt | SHA-256 |
|---|---|
| `20260910T164612_267481Z/receipt.json` | `9686e2a09b156b30cf2ca0244e8b1909aa1f0e03e01ec9fed0d0c1ce952fcf67` |
| `20260910T165320_099157Z/receipt.json` | `599256bbc66db030361297d84550ea3edcf45b6b0395c16a0671d55bc461f0cf` |
| `20260910T165833_044314Z/receipt.json` | `1c5006a3a3996487c5f9b05460fd7e2d6e4bb4e6d59110aba9f71750d776559d` |
| `20260910T170004_394093Z/receipt.json` | `589ed69dd3f6c2fc81f84132910ab2a1baaaf0dc65e7c81767fcb9cc9491d907` |
| `20260910T170214_177906Z/receipt.json` | `359519d455bd5736807878f45b85418aca4892efcabcac5c858ac99fe0aa0bcf` |
| `20260910T170310_319161Z/receipt.json` | `5dc70b65809593512da29a1e8f8ba6933fb50208e9f6f3586ba68e60ec98917d` |

Supporting sources inspected: `GenericCompactLaplacianProduct_v1`,
`GenericCutoffLaplacianDivergenceTests_v1`, `GenericBoundedSmoothMultiplier_v1`,
`GenericDistributionDivergenceConverse_v1`, `FiniteDimSmoothCutoff_v1`,
`GenericWeakEllipticGain_v1`, and `LaplacianSobolevBridge_v1`; also the pinned
Mathlib `Analysis/Distribution/Sobolev.lean` definitions and Bessel/derivative
lemmas. Previously verified global product transport was reused. The reviewer
authored some of that prior product transport, so this review is not wholly
independent of every dependency, although the nine new local elliptic sources
were authored by another agent. Agent agreement is not additional proof.

The checked evidence uses the pinned development object cache and does not
extend the sealed 671-target isolated desktop source-rebuild claim. The
historical preservation anchor is frozen `rwa_proof/RWA_THEOREM.md`, SHA-256
`d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. This review changes no frozen or successful
proof, source, status, or audit record.
