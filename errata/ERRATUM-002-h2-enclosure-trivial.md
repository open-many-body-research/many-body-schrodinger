# ERRATUM-002: S3-004, the H₂ enclosure is trivial

- **Date:** 2026-09-11
- **Affected claim:** S3-004
- **Affected file:** `archive/v1.0-research-notes/reports/H2_CERTIFICATION.md` (unfinished: its final-certificate section was never filled in)

## What was claimed
A certified enclosure $[-2.64, -1.888470852763]$ Ha of the H₂ electronic ground energy at $R = 1.4$ bohr (width 0.7515 Ha), produced from a 64-function correlated-Gaussian trial.

## What is wrong
The lower endpoint $-2.64 = -66/25$ is the a-priori noninteracting bound. The Temple lower bound from the trial is
$$m - \frac{v}{\beta - m} \approx -1.8885 - \frac{0.3964}{0.0685} \approx -7.68,$$
which is weaker still. The trial variance is dominated by the cusps that Gaussians miss, and the separator margin $\beta - m \approx 0.068$ Ha is small.

The upper endpoint is a valid variational bound, about $2.9\times10^{-4}$ Ha above the literature value. The 128- and 288-function runs were interrupted and never completed.

## Corrected statement
There is **no non-trivial certified H₂ lower bound** in this repository. That is open problem S3.1.

## Registry change
S3-004: tier X.
