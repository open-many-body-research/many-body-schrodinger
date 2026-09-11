> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Smooth affine compact finite jet checkpoint

Created 2026-09-10. This is new Rung 2 initialization work. Original T02 remains unverified.

## Historical provenance

Frozen context: `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`,
as recorded in `THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`.
Frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`; annotated tag
`theorem-t-proof-freeze-2026-09-09`. No frozen artifact or previous PASS source
was edited. This checkpoint adds a prerequisite and does not revise a frozen
mathematical claim.

## New result

Module `lean/SmoothAffineCompactFiniteJets_v1.lean` contains three declarations
in `TheoremT.Continuum`:

- `smooth_compact_finite_iteratedFDeriv_bound` derives a common bound for
  derivative orders `k ≤ m` from `ContDiffOn` on an open set and compactness of
  `K` inside that set.
- `smooth_affine_compact_finite_iteratedFDeriv_bound` chooses `M ≥ 1` before
  `eps ∈ [0,1]`, with all spatial derivative norms of orders `k ≤ m` bounded by
  `M` for both `f0 + eps * f1` and `eps * (f0 + eps * f1)`.
- `smooth_affine_compact_finite_source_bound` uses the same quantifier order and
  additionally bounds the complex source `(f0 + eps * f1) • a0` by `M * ‖a0‖`
  for every `a0 : ℂ`.

The domain is a fixed normed real vector space. The hypotheses contain actual
smoothness (`ContDiffOn ℝ ∞`), openness, compactness, and inclusion, with no
assumed derivative norm bound. Empty compact sets are admitted. The bound
includes order zero. The complex source uses real scalar multiplication and
the complex norm; derivative norms are full continuous multilinear operator
norms.

## Verification and hashes

Compilation PASS:
`logs/development/SmoothAffineCompactFiniteJets_v1-20260910T205003_004357Z.json`.

Strict v5 expanded-statement and axiom audit PASS:
`audits/formal_semantics/20260910T205013_796153Z/receipt.json`.
All three declarations were discovered and audited; no printer ellipses,
forbidden tokens, or unexpected axioms were present. Source and object were
unchanged during audit. Exact expanded types were reviewed in the audit log.
All three declarations depend only on `propext`, `Classical.choice`, and
`Quot.sound`.

- Source SHA-256: `2e8686e7ccec318769125b4ecb540a4879ad884e6371ed1949365fe86cda5534`.
- Object SHA-256: `18134e7c36021f5b89ed6b4de232e9d0c78928db7f801fd12b839a444b2b8303`.
- Expanded audit source SHA-256: `2330b2fbb9b1f4016582c1652664309faec0d92461703c76f47d8312d840ab61`.
- Expanded audit log SHA-256: `1cbff86765da45d21f42d98a316eb86b0c838c2ff4d9acb95fd6c29574299ca5`.

The compiler and auditor used the pre-existing pinned dependency object cache.
This checkpoint is not a source rebuild of those dependencies.

## Scope limit

The constant may depend on the finite reserve `m`, the compact set, the open
set, and both input functions. Its value is not computed. There is no
all-orders uniform constant, factorial dependence, analytic estimate, H12
claim, weak solution existence claim, or convergence certificate. Physical
nuclear/pair coefficient identification and any subsequent PDE application
require separate theorems. This checkpoint does not close original T02.
