# S3: Certified energy intervals

**Scope.** For concrete systems, produce rational intervals $[\ell, u]$ that are *guaranteed* to contain the true ground energy of the continuum Hamiltonian, and make them as narrow as possible. Upper bounds come from the variational principle. Lower bounds are the hard part: they need a proved spectral separator $\beta$ and a certified residual (Temple, Kato, Lehmann).

**What counts.** The deliverable is an exact or outward-rounded certificate together with a checker that does not trust the optimizer. See [CONTRIBUTING.md](../../CONTRIBUTING.md) §5.

## Current best (v1.0 foundation)

| System | Enclosure (Ha) | Width | Claim | Tier |
|---|---|---|---|---|
| He | $[-2.903724385192751581540207,\ -2.903724377006065467379698]$ | $8.19\times10^{-9}$ | [S3-002](../../claims/cards/S3-002.md) | C (moment formulas P1) |
| He | $[-2.903725202862,\ -2.903724370072]$ | $8.33\times10^{-7}$ | [S3-001](../../claims/cards/S3-001.md) | C (moment formulas P1) |
| H₂, $R=1.4$ bohr | no non-trivial lower bound. The upper bound $-1.888470852763$ is valid but unpackaged. | n/a | S3-004 | X |
| H⁻, Li, … | none | n/a | n/a | n/a |

For comparison, the best non-rigorous helium value is $-2.903724377034119598\ldots$ (Schwartz 2006; Nakashima–Nakatsuji 2007). Published Temple-type lower bounds are claimed to reach many more digits. What this repository adds is full, dependency-free reproducibility with exact arithmetic.

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S3.1 | **Non-trivial H₂ lower bound** at $R = 1.4$ bohr, clamped nuclei, nuclear repulsion excluded | A certificate of width $< 10^{-3}$ Ha. With the current separator this requires trial variance $\le 4.9\times10^{-5}$, about 8,200× below the best Gaussian trial so far. Stretch goal: $< 10^{-5}$ Ha. | open |
| S3.2 | **Better H₂ separator** | A proved lower bound $\beta(R)$ on the second eigenvalue in the $^1\Sigma_g^+$ sector at $R=1.4$, with $\beta \ge -1.6$ Ha (current: $-1.82$). Because the width scales as $1/(\beta-m)$, this cuts every H₂ width by about 4×. | open |
| S3.3 | **Cusp-capable H₂ trials** | James–Coolidge or Kołos–Wolniewicz-type trials with exact or interval $\lVert H\Phi\rVert^2$ moments, independently checked on 100 random rational test functions | open |
| S3.4 | **Helium below $10^{-12}$ Ha** | Trial, certificate, checker log, and a replay on a second machine | open |
| S3.5 | **Sharper helium separator** | A proved $\beta \ge -2.15$ Ha for the $^1S$ sector (true 1s2s $^1S$ ≈ −2.1459) | open |
| S3.6 | **H⁻** ($Z=1$; the rank-one separator fails) | Any certified enclosure of width $< 10^{-4}$ Ha, with a proved separator | open |

## Where to look
- [`certificates/`](../../certificates/): checkers and certificates.
- [`archive/v1.0-research-notes/h2/`](../../archive/v1.0-research-notes/h2/): the H₂ separator proof and the moment theory (P1).
- [`archive/v1.0-research-notes/reports/RATE_DICTIONARY_DECISION.md`](../../archive/v1.0-research-notes/reports/RATE_DICTIONARY_DECISION.md): how the helium dictionaries were compared.
