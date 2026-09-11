> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../claims/registry.yaml) and [`STATUS.md`](../../../STATUS.md). File paths refer to the private workspace layout.

# Bounded H₂ kernel performance audit

**EMPIRICAL.** Twelve primitive pairs from `trial_ecg_residual288_q128.json` were tested using the actual rational `pair_moments` implementation at 128 bits, with fifteen inverse-product kernels per completed pair. Each pair had a twenty-second total budget across the three tolerances; value-dependent caches were cleared between cases. No matrix was assembled. The measured engine was frozen at SHA256 `ae69b630f8d4261caf7b0266ba899a206d456ae31d6f829a9f1ad7a0bfd897be` throughout this audit. Raw exact widths, parameters, trial hash, diagnostics and empirical timings are in `frozen_pair_benchmark.json`; its final two skipped rows were not flushed, but follow from the stated time-budget policy and final log.

Times below are seconds. “Cap after x” is a censored run that did not complete, **not** its total runtime. A dash means it was skipped because that pair exhausted its total budget. All completed cases met their requested widths for all fifteen kernels.

| Pair class | Primitive indices | 10⁻³ | 10⁻⁵ | 10⁻⁸ |
|---|---:|---:|---:|---:|
| core/core | 0, 0 | 0.160 | 0.181 | 0.272 |
| core/core | 0, 15 | 0.224 | 0.287 | 0.390 |
| core/core | 6, 31 | 7.736 | 9.850 | Cap after 2.411 |
| core/core | 32, 63 | 0.224 | 0.224 | 0.315 |
| core/cusp | 0, 64 | 0.261 | 0.292 | 0.418 |
| core/cusp | 15, 95 | 16.104 | Cap after 3.897 | — |
| core/cusp | 31, 159 | Cap after 20.002 | — | — |
| core/cusp | 6, 287 | Cap after 20.002 | — | — |
| cusp/cusp | 64, 64 | 0.249 | 0.280 | 0.374 |
| cusp/cusp | 71, 127 | Cap after 20.003 | — | — |
| cusp/cusp | 191, 223 | Cap after 20.003 | — | — |
| cusp/cusp | 255, 287 | Cap after 20.001 | — | — |

For the five pairs completing all tolerances, loosening 10⁻⁸ to 10⁻³ yielded approximately 1.4–1.8× speedups, not tenfold. Several cusp pairs remained expensive at 10⁻³. This fixed local-tolerance experiment does not test the matrix checker's coefficient-weighted error budget, so it does not determine how many negligible pairs that budget can omit using the universal Cauchy–Schwarz enclosure.

## Identified bottleneck and bounded improvement

The isolated inverse product for primitive pair (6,31), potential pair (0,2), needed only two quadrature cells at 10⁻³, but its original Boys evaluation consumed 0.554 of 0.586 CPU seconds (94.6%). Its sixteen arguments lay between approximately 178.05 and 179.83. Exact argument intervals and raw timing observations are saved in `frozen_kernel_profile.json`.

**PROVEN (paper derivation only).** For t>0, the positive Gaussian tail gives

    sqrt(π)/(2sqrt(t)) − exp(−t)/(2t) ≤ F₀(t) ≤ sqrt(π)/(2sqrt(t)).

The complete proof and interval endpoint construction are in `quadrature.md`. The authorized implementation uses this enclosure only inside the positive reduced integrand when the complete argument interval is at least 128. It retains the full tail width and rounding error. The prolate `erfc` subtraction is unchanged. These analytic claims have executable rational arithmetic checks but are not Lean-checked.

**EMPIRICAL.** The bounded old/new kernel regression gave:

| Local tolerance | Original CPU seconds | New CPU seconds | Speedup | Cells in both |
|---|---:|---:|---:|---:|
| 10⁻³ | 0.594 | 0.0176 | 33.8× | 2 |
| 10⁻⁸ | 1.238 | 0.0364 | 34.0× | 4 |

At each tolerance, exact old/new output intervals overlap and both meet the requested width. The full engine self-tests, including threshold-crossing arguments, large-argument Boys comparisons, and near-perfect-correlation resource caps, passed. Records are in `line_tail_benchmark.json`, `line_tail_benchmark.log`, and `gaussian_integrals_test.log`. The optimized engine is frozen at SHA256 `b8316ec0a3d19afa96d206bba3391e37e0fa5daed2a5a17723347189eeeca74b`.

This kernel speedup does not establish a whole-matrix speedup. High prolate cell counts and difficult near-proportional covariance bounds remain distinct bottlenecks in the censored examples. No broader performance experiment was run after the bounded regression.
