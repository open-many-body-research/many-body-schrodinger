> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local-grid v2 execution checkpoint

The strongest new result is the paper-supported deterministic requested-width
atomic algorithm with bit cost 2^O_(N,Z)(p) for each fixed finite N,Z, using the
same full continuum spectral target and gap-free localization as v1.
`LOCAL_GRID_AND_BIT_COST_v2.md` gives the exact hypotheses, local-LCM correction,
explicit sufficient arithmetic precision, intermediate rational operand bounds,
and cost model. This is not polynomial precision cost, uniform growing-N
efficiency, a Lean theorem, or a claimed novelty result.

The source change is narrow: each canonical integral now resolves only its
own six or twelve scalar sine indices. It preserves the complete physical
trial subspace and all clipping, complement and localization estimates.
The unnecessary global lcm(1,...,K) had imposed an extra exponential in K;
its removal changes the proved cost without inventing a faster observed run.

## Executed evidence

`test_local_grid_v2.py` passed all four groups:

1. Every interval matrix entry, spin orbital, occupation and trial kinetic
   value agrees exactly with v1 for a 120-dimensional N=2, K=2 aligned-grid
   case.
2. An N=1, K=3 constant-kernel case uses several different local grids and
   all 54-by-54 entries contain the exact diagonal kinetic-minus-potential
   matrix, including zero off-diagonal entries.
3. All 765 independently expanded small determinant matrix entries agree
   with the v2 creation/annihilation assembler.
4. The requested-width composition uses no global node LCM, and actual
   vacuum box and full-space certificates return [0,0].

`test_precision_cost_bound_v2.py` passed three groups: 384 exact binary-log
brackets, 900 sine-overlap width checks plus 54 exact-radius clipped-inverse
checks, and 180 atomic level plans checking the explicit sufficient-bit
inequalities. These finite tests supplement the paper bound, not prove the
all-input inequalities by sampling.

The positive-N certificate
`occupation_N2_K2_M8_Jn16_Jp8_v2.json` used N=2,Z=2,R=1,M=8,K=2,
Jn=16,Jp=8,b=24. It has all 120 fermionic occupations. Its matrix and resulting
enclosures agree exactly with the sealed corresponding v1 certificate, as
recorded in `local_grid_certificate_comparison_v2.json`. The full-space interval
is [-4,0]; the box upper endpoint is 28741091/33554432. The matrix computation
took 21.206684 seconds with 28,524,544 peak-RSS bytes on this shared macOS
Python 3.14.7 process. It used 36 nuclear and 666 pair integral cache entries,
including parity zeros, and 11 rational PSD bisection decisions. These are
observations; no speed improvement or narrow helium result is claimed.

`verify_local_grid_v2.py` then copied the required source files and certificate
to a fresh temporary directory and ran Python with `-I -B`. Source compilation,
both test suites, complete recomputation of the 120-by-120 certificate, vacuum
certificate generation/checking, and rejection of a tampered continuum energy
endpoint all passed. `isolated_local_grid_rebuild_result_v2.json` records the
commands, return codes, source hashes and outputs. Elapsed time was 31.392916
seconds. No disk bytecode, Lean artifact, or third-party package cache was used;
in-process arithmetic memoization was used. This is source reproducibility of
the Python branch, not a rebuild or formal verification of the Lean continuum
theory. The checker deliberately shares the arithmetic implementation; the
independent determinant expansion and prior primitive reviews provide separate
bounded checks, not an independent proof of the Python runtime.

## Feasibility and next frontier

`atomic_N2_Z2_p1_cost_plan_v2.json` computes only scalar schedules. Even at the
requested full-space helium width 1/2, the N=1 predecessor and N=2 box dimensions
are respectively

    7003487674200190902295838416
    5392261830503950602332264425158556705121515470336.

The sufficient precision bounds are 2418 and 2210 bits, each reached by a
4096-bit doubling step. These values isolate the bottleneck: the number of
matrix entries and integration cells, not an unbounded hidden rounding search.
No positive-N conservative requested-width execution was attempted. The actual
positive-N results remain finite-stage enclosures, and the all-input result
remains supported by the explicitly stated paper proofs.

Next useful work is feasible sharper helium certification using the audited
physical moment machinery and a rational finite trial, or improving the
localization/complement constants and discretization. The original Theorem T
analytic RATE, its exact prescribed dictionary schedule and its full Lean
verification remain separate unresolved obligations.

All v1 and frozen artifacts are preserved byte-for-byte. Exact frozen
provenance and the versioned runtime correction are recorded in the companion
cost proof and earlier sealed manifests.
