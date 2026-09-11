# Certificates

Each subdirectory holds rational inputs, a checker, and the certificates it produced.

- **Standard library only.** Every checker is Python 3 standard library: `fractions.Fraction` plus outward-rounded dyadic intervals from `certified_interval.py`.
- **No floating point.** Floating-point values never enter a certificate inequality, and trial files are rejected if they contain JSON floats.

| Directory | System | Best width (Ha) | Claim |
|---|---|---|---|
| [`helium-dyadic-dictionary/`](helium-dyadic-dictionary/) | He ground state | $8.19\times10^{-9}$ | [S3-002](../claims/cards/S3-002.md) |
| [`helium-ground-state/`](helium-ground-state/) | He ground state | $8.33\times10^{-7}$ | [S3-001](../claims/cards/S3-001.md) |

## Verify

```bash
python3 certificates/run_checks.py --quick   # seconds; runs on every pull request
python3 certificates/run_checks.py --full    # every certificate plus the independent algebra audit; ~15 minutes
```

`run_checks.py` re-derives each certificate in a temporary directory from the published trial. It then requires the result to match the published certificate on every mathematical field. Run metadata (timings, interpreter version, code hashes) is not compared.

## What the checker trusts

**Trusted:**
- the Python standard library and interpreter;
- the closed-form moment formulas, derived in `helium-ground-state/THEORY.md` (a paper proof, tier P1, spot-checked by `independent_audit.py`);
- the spectral separator $\beta = -5/2$, proved in Lean ([S2-002](../claims/cards/S2-002.md)).

**Not trusted:** the selection and optimization scripts (`select_*.py`, `run.py`'s screening stage), any published reference energy, and floating point.

## Provenance note

These files come from the v1.0 foundation's private workspace. Before publication, three kinds of change were made:

- **Identifying metadata removed.** The machine `host` field was deleted from the certificates and trial files. For the dyadic dictionary, each certificate's `trial_sha256` was updated to match its redacted trial file.
- **Import paths.** Import paths were changed to point at the new directory layout.
- **Nothing mathematical changed.** No trial coefficients, moments, or endpoints were changed. `run_checks.py --full` reproduces every mathematical field.

`MANIFEST.json` in each directory lists the SHA-256 of every published file.
