> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Seven-dimensional order-12 multiindex checkpoint

Created 2026-09-10. This is a finite combinatorial prerequisite for later
H12 norm assembly. Original T02 remains unverified.

Historical context: frozen `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, from
`THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`; frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. No frozen artifact or prior PASS source was
changed.

## Audited definitions and results

The import target is `lean/H12MultiIndexCount_v2.lean`.

`boundedMultiIndex d m` is exactly the subtype of functions `Fin d → ℕ` whose
coordinate sum is at most `m`. An explicit equivalence adds a slack coordinate
`m - sum alpha` to obtain functions on `Fin (d+1)` with sum exactly `m`.
The existing `Sym.equivNatSumOfFintype` and `Sym.card_sym_eq_choose` then prove
the cardinality `(d+m).choose m`.

`h12MultiIndices` is the universal finite set of `boundedMultiIndex 7 12`.
`h12MultiIndices_card` proves its cardinality is exactly `50388` by evaluating
the small factorial formula for `19 choose 12`. No multiindex list is expanded
or enumerated. Completeness and total-order declarations expose that every
seven-dimensional nonnegative multiindex of total order at most 12 is included.

For any seminormed additive group and any family `v` on this finite index type,
`h12MultiIndexNormSq v` is the sum of `‖v alpha‖^2`.
`h12MultiIndexNormSq_le` proves this sum is at most `50388 * C^2` from
`∀ alpha, ‖v alpha‖ ≤ C`. There is no extra assumed Sobolev estimate.

## Verification and preservation

Compilation PASS:
`logs/development/H12MultiIndexCount_v2-20260910T210225_497011Z.json`.
Strict v5 audit PASS for all 12 declarations:
`audits/formal_semantics/20260910T210236_251361Z/receipt.json`.
Exact expanded types were reviewed. No forbidden source token, ellipsis, or
unexpected axiom appeared; source and object remained unchanged. All local
declarations use only `propext`, `Classical.choice`, and `Quot.sound`.

- Source SHA-256: `9c1078f7dcfb025bd1cb4e42a84de610afe3140e43eccc26edca42e612a02c4f`.
- Object SHA-256: `5d5dc464f7a934ad0adaeb3f5d1a9ae68db72eac7313651d2b06060c7b4a87c9`.
- Expanded audit source SHA-256: `a0129b4df67e476c870f6629c3cfb711c6054f5a3635c5088668a1cafa5941e1`.
- Expanded audit log SHA-256: `616c025cb49093bf95cb5543323a5b140db37cfec2fdab379487e03c38522b9a`.

Version 1 compiled successfully, but the conservative v5 source discovery
rejected its named `instance` command before an audit could run. Its PASS bytes
were preserved. Version 2 uses the supported `@[instance] def` form with the
same mathematical content. Lean emits a nonfatal semireducibility warning for
this class-valued definition. Import version 2 only: the two versions expose
the same declaration names and should not be imported together.

This reused the pinned dependency object cache without rebuilding dependencies.
No actual derivative family, weak derivative identification, PDE estimate,
Sobolev regularity theorem, or final H12 bound has been proved here.
