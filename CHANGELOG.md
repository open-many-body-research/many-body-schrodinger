# Changelog

## v1.0-foundation (2026-09-11)

This is the first public release: a curated, audited snapshot of earlier private, AI-assisted research.

**Established**
- **Lean (L), 7 claims.** Kato-type self-adjointness and ground-energy identification for atoms (S1-001), the non-attracting case (S1-002), hydrogen (S1-003, S1-004), the abstract ground branch and continuum Temple enclosure (S2-001), the two-electron and helium ground branch with separator $-5Z^2/8$ (S2-002), and the physical Temple enclosure (S2-003). The library has 817 modules with pinned Lean and Mathlib.
- **Certified computation (C), 2 claims.** Helium enclosures of width $8.3\times10^{-7}$ Ha (S3-001) and $8.19\times10^{-9}$ Ha (S3-002). All 16 published certificates were re-derived before release.

**Recorded, not established**
- **P1, 12 claims.** Paper-level claims, including the triple-collision analyticity and dictionary-rate claims (S8-001, S8-002), which need human expert review.
- **Open (O), 2 claims.** Theorem T (S2-008) and continuum hardness (S7-001).
- **Withdrawn (X), 4 claims.** The "Theorem T PROVEN" label ([ERRATUM-001](errata/ERRATUM-001-theorem-t-not-proved.md)), the trivial H₂ enclosure ([ERRATUM-002](errata/ERRATUM-002-h2-enclosure-trivial.md)), and trivial results that had been presented as results ([ERRATUM-003](errata/ERRATUM-003-trivial-results.md)).

**Left out of the release**
- The Hubbard-model exploration. It uses `native_decide` and gives weak bounds.
- Full-text copies of papers.
- Agent logs, build caches, and machine-identifying metadata.
