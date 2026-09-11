# S8: Regularity of eigenfunctions and approximation rates

**Scope.** The structure of eigenfunctions at particle coalescences (cusps, logarithms, analyticity), and rigorous approximation rates for explicit bases with explicit constants.

## Current best (v1.0 foundation)

| Claim | Result | Tier |
|---|---|---|
| S8-001 | Weighted all-order (analytic-type) bounds for the helium ground state's extracted remainder, uniformly up to the triple-collision vertex | P1, **needs expert review** |
| S8-002 | $H^2$ approximation rate $C e^{-c n^{1/3}}$ for helium by an explicit dyadic-exponent dictionary (existence only) | P1, **needs expert review** |
| S8-003 | "Theorem C": in any fixed-exponent Hylleraas family, the residual is $\ge c(n+1)^{-72}$ | P1 |

**Why S8-001 matters.** If it is correct, it goes beyond the published regularity at the triple point: $C^{1,1}$ factorization (Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Østergaard Sørensen 2005), and analyticity at isolated pair collisions (same authors, 2009). It is also the analytic foundation of the Theorem T program (S2). So far only AI agents have reviewed it.

**Formal progress.** `lean/Foundation/` also contains Lean modules on the physical ground state's regularity and decay: rotation invariance, boundedness, the exponential $H^2$ tail, and the Kato–Stummel/Grušin machinery. Those modules have no statement cards yet. Writing cards for them is open problem S8.5.

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S8.1 | **Human referee report on S8-001** | A review record (see `reviews/TEMPLATE.md`) of [`rwa_proof/RWA_THEOREM.md`](../../archive/v1.0-research-notes/rwa_proof/RWA_THEOREM.md), [`UNIFORM_ANALYTIC_AUDIT.md`](../../archive/v1.0-research-notes/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md) and the Kato–Stummel descent notes in [`continuation/audits/`](../../archive/v1.0-research-notes/continuation/audits/). It should confirm the result or exhibit a gap. | open |
| S8.2 | **Human referee report on S8-003** | A review, or a sharper exponent than 72 | open |
| S8.3 | **Explicit constants for S8-002** | Numerical $C, c$, or a lower bound refuting the rate | open |
| S8.4 | **Check a claimed misprint** | The notes ([`ISSUE_KS_SOURCE_DEGREE_v2.md`](../../archive/v1.0-research-notes/continuation/audits/ISSUE_KS_SOURCE_DEGREE_v2.md)) claim that one coefficient bound in arXiv:0806.1004v1 (eq. 4.41) is false as literally stated, and that the headline theorem is unaffected. Check it against the published journal version *before* anyone asserts it publicly, and contact the authors if it holds up. | open |
| S8.5 | **Statement cards for the regularity modules** | Cards for the decay and regularity Lean modules, with a definitions audit | open |
