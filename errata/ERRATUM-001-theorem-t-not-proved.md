# ERRATUM-001: S2-008, "Theorem T" was labeled PROVEN; it is not proved

- **Date:** 2026-09-11 (recorded at publication of v1.0-foundation)
- **Affected claim:** S2-008 (Theorem T)
- **Affected file:** `archive/v1.0-research-notes/reports/RWA_REPORT.md`, sections 8–9 ("THEOREM T STATUS: PROVEN", with bit-cost exponent 2256)

## What was claimed
A pre-publication report stated that a deterministic algorithm computes the two-electron ground energy to $p$ bits in $C_Z(p+1)^{2256}$ bit operations, and marked the result PROVEN.

## What is wrong
The composition relied on steps that were never established:

- **Human review.** The analytic inputs (S8-001, S8-002) have been reviewed only by AI agents.
- **Algorithm.** No coefficient-selection algorithm has a correctness proof.
- **Verification.** Moment evaluation, the finite solver, termination, and the bit-cost model have not been verified.

The project's own later audits already downgraded the claim to "not established".

## Corrected statement
Theorem T is **open** (tier O). See [sectors/S2-two-electron-theory/README.md](../sectors/S2-two-electron-theory/README.md) for what is missing.

## Registry change
S2-008: tier O. The frozen report stays in the archive unchanged apart from a warning banner.
