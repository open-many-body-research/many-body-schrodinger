# Helium ground state: Hylleraas-type trials (orders 6–20)

| Certificate | Trial | Dimension | Enclosure (Ha) | Width |
|---|---|---|---|---|
| `certificate_6_512.json` | `trial_6.json` | 50 | [−2.904205402197, −2.903722991582] | 4.8e-4 |
| `certificate_10_512.json` | `trial_10.json` | 161 | [−2.903780097670, −2.903724300957] | 5.6e-5 |
| `certificate_residual_8_512.json` | `trial_residual_8.json` | 95 | [−2.903791896940, −2.903723192896] | 6.9e-5 |
| `certificate_residual_10_512.json` | `trial_residual_10.json` | 161 | [−2.903749021308, −2.903724007465] | 2.5e-5 |
| `certificate_residual_14_512.json` | `trial_residual_14.json` | 372 | [−2.903729342076, −2.903724319968] | 5.0e-6 |
| `certificate_residual_20_{512,768}.json` | `trial_residual_20.json` | 946 | [−2.903725202862, −2.903724370072] | 8.3e-7 |

The `residual` trials were chosen to minimize the certified residual. The others were chosen by the Rayleigh quotient. Selection is irrelevant to correctness, because the checker recomputes everything from the rational coefficients.

## Files

| File | Role | Trusted? |
|---|---|---|
| `check_trial.py` | Checker: exact moments and Temple interval | yes |
| `hylleraas.py` | Exact Hylleraas polynomial algebra and moments | yes |
| `certified_interval.py` | Outward-rounded dyadic intervals, $\log 2$ and $\pi$ enclosures | yes |
| `independent_audit.py`, `independent_audit.md` | A separate derivation of the moment formulas, checked on exact test identities | audit |
| `THEORY.md` | Paper derivation of the moment formulas and the continuum argument (P1) | paper |
| `select_trial.py`, `select_residual_trial.py` | Produced the trials | **no** |

## Run one check

```bash
cd certificates/helium-ground-state
python3 check_trial.py trial_residual_20.json --bits 768   # writes certificate_20_768.json; about 3 minutes
```
