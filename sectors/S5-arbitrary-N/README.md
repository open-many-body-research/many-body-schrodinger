# S5: Algorithms for arbitrary N

**Scope.** Certified algorithms for the ground energy of general atoms and molecules: computability, explicit cost bounds, box localization, and verified implementations.

## Current best (v1.0 foundation)

| Claim | Result | Tier |
|---|---|---|
| S5-001 | Gap-free box localization: $`\min\{\lambda_N(R), E_{N-1}-NZ/R\} - N\pi^2/(8R^2) \le E_N \le \min\{\lambda_N(R), E_{N-1}\}`$ | P1 |
| S5-002 | Computability to $`2^{-p}`$ at explicit cost: $`2^{O_{N,Z}(p)}`$ for atoms, $`2^{O((N+1)(p+N+L+1))}`$ for rational molecules | P1 |
| S5-003 | Executed box enclosures (widths 0.24–12 Ha) and the "fast two-center class" | X (trivial) |

Computability is folklore. The explicit bookkeeping is the only contribution here, and nothing of practical width has been executed.

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S5.1 | **A useful run** | Use a general-$`N`$ certified method to produce a helium enclosure of width $`< 10^{-2}`$ Ha *without* the special two-electron separator | open |
| S5.2 | **A verified implementation** | A Lean (or other verified) implementation of the box solver's finite stage, proved sound against the S1 operator | open |
| S5.3 | **Better than $`2^{O(p)}`$** | For any fixed $`N \ge 3`$, a certified algorithm with cost polynomial in $`p`$ (the $`N`$-electron analogue of Theorem T) | open |
