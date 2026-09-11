> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Executed N=2 stage and review disposition

The reviewed exact-rational procedure produced the paper-supported continuum
interval

`[-4, -33192927779/34359738368]`

for the N=2,Z=2 fermionic Dirichlet-box ground energy on `(-2,2)^6`, and also for
the full-space helium ground energy. Its exact width is
`104246025693/34359738368` (approximately 3.03396). This is a broad computation
that exercises the actual pair interaction; it does not improve physical
energy accuracy over established analytic trials. The lower endpoint is the
elementary independent-hydrogen bound. The evaluated complement/restoration
estimate is weaker at this stage. There is no Lean verification claim.

The proof and exact input class are in `TWO_ELECTRON_STAGE_v1.md`. At collision
radius zero the clipped inverse-distance representative equals M. This changes
no integral or multiplication operator because the nuclear and pair collision
sets are null; the representative also makes the clipped function continuous.
Full continuum graph/domain claims are not inferred from this executable.

| Stage | M | nuclear J | pair J | time (s) | exact full-space/box upper |
|---|---:|---:|---:|---:|---|
| `n2_Z2_R1_M8_K1_Jn32_Jp16_v1.json` | 8 | 32 | 16 | 5.0873 | `-6855948423/17179869184` |
| `n2_Z2_R1_M16_K1_Jn64_Jp32_v1.json` | 16 | 64 | 32 | 17.4182 | `-33192927779/34359738368` |

Both use R=1, interval bits=32, eta=1, and one normalized opposite-spin
determinant. Peak resident memory was 25,001,984 and 24,969,216 bytes respectively.
The second upper endpoint is approximately -0.96604. Exact rationals carry the
certificate; timings, memory and decimal renderings are diagnostics.

The implementation source is `exact_two_electron_stage_v1.py`, SHA-256
`8f5688e38d89b9cf75ebb8257edf339c12a1bb7a231d71f638e8978246e174b4`. Its primitive
dependency is `exact_box_v1.py`, SHA-256
`f1358f9f63f025554128a20ad2d464934509a6363ae49bc028cba92e2673ad58`.

The root researcher read the complete source and mathematical argument and
accepted the paper-supported exact-rational continuum interpretation, explicitly
retaining the non-Lean and shared-checker trust boundary. The independent
review is `INDEPENDENT_N2_REVIEW_v1.md`; its separate computation
`independent_n2_checks_v1.py` checked 9,780 explicit six-dimensional cell pairs
at J=1,2,3,4 for both nonconstant and exactly constant clipped interactions.
Every interval endpoint exactly agreed with the grouped convolution output;
`independent_n2_checks_v1.json` records PASS. Agreement is review evidence,
not formal proof by consensus.

The four grouped implementation tests pass: a brute six-dimensional rational
convolution identity, normalization of difference probabilities, constant
clipping for both interaction types, and an exactly known constant-potential
Slater compression/complement. `check_n2_M8_Jp16_v1.json` and
`check_n2_M16_Jp32_v1.json` record successful full recomputation of every integral
and scalar bound, with exact source-hash matching.

`isolated_two_electron_rebuild_result_v1.json` records PASS after copying only
three sources and the first certificate to a fresh temporary directory. Python
`-I -B` recompiled source, reran tests, regenerated the first certificate, and
checked both supplied and generated certificates. Every exact mathematical
field reproduced. No third-party dependency, disk numerical cache, or bytecode
cache was used. Only in-process mathematical memoization was reused within a
single process. This establishes source replay in the declared CPython
environment, not a Lean theorem or an independent checker kernel.

This rung implements a useful finite pair-interaction stage. A complete
arbitrary-precision N=2 bounded-box implementation, all-order antisymmetric
matrix construction, formally checked integration, and improved practical
lower estimates remain open. The next computation is a new N=3 finite Slater
stage with actual signed exchange integration. It does not reuse the N=2
nondegenerate kinetic-complement threshold without checking degeneracy.

Frozen provenance and predecessor hashes are stated in `TWO_ELECTRON_STAGE_v1.md`;
all frozen files remain unchanged.
