> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Moment representation clarification, version 1

Date: 2026-09-09. This is a terminology correction with no change to the moment recurrence, dictionary, numerical endpoints, or claimed rate.

Frozen snapshot: `THEOREM_T_FREEZE_2026-09-09_212604/`; commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`; tag `theorem-t-proof-freeze-2026-09-09`.

- `rwa_proof/THEOREM_T_COMPOSITION.md` — SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`.
- `RATE_DICTIONARY_DECISION.md` — SHA-256 `d9d15d0412ae5c8148aeeff6e264c8a2c0ae23df8dc8324929e698652146f303`.

In `rwa_proof/THEOREM_T_COMPOSITION.md:49`, “three-dimensional moment field” should be understood in new work as the rational linear span

    M = {a + b log 2 + c pi^2 : a,b,c in Q}.

The datatype of coefficient triples is Q^3. Its evaluation map into R is linear; no injectivity or Q-linear independence of the three real constants is needed or established by the computation. The evaluated span has dimension at most three.

This span is not a field. If it were, it would be a finite-dimensional field extension of Q and every element would be algebraic over Q. It contains pi^2, which is transcendental since pi is transcendental. Therefore the field terminology is mathematically incorrect. This uses the classical transcendence of pi, not an assertion about algebraic independence of pi and log 2.

The arithmetic actually required remains valid: add triples, scale by rational numbers, and evaluate triples using independently enclosed constants. Rational trial contraction preserves M. Normalization uses rational G; A is rational; matrices for the finite spectral solve are rational interval approximations. No closure of M under arbitrary products, inverses, or exact transcendental-sign decisions is used. The larger rational function field Q(log 2, pi^2) must not be substituted, since that would enlarge the representation and require different algorithmic operations.

Related occurrences of “field” in `RATE_DICTIONARY_DECISION.md:65` and in the composition's coefficient descriptions receive the same clarification. This correction does not discharge any continuum, RATE, termination, or bit-cost proof obligation. Those statuses remain as recorded in the new audit ledger.
