> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Molecular computation checkpoint

The new input class consists of finitely many distinct rational nuclear
positions with positive rational charges, finite N, and precision p. The
implemented routines enclose either the electronic continuum spectral
infimum or the clamped-nucleus total energy with separately certified nuclear
repulsion. The paper proof supplies termination for every finite mathematical
input in the declared unbounded integer model. No positive-N conservative
requested-width execution, Lean implementation proof, binding conclusion,
unique ground vector, or observable accuracy is asserted.

`MOLECULAR_COMPUTABILITY_v1.md` states the operator, actual weak H2 fermionic
domain, box form problem, translated Hardy/clipping bounds, full-space IMS
recursion, and trust limits. Nuclear charge rounding Q=ceil(sum z_l) enters
only conservative error constants; the integral matrix uses the exact
individual charges and centers. The additional
`UNIFORM_MOLECULAR_SIZE_BOUND_v1.md` tracks all input sizes and proves the
paper bit bound 2^O((N+1)(p+N+L+1)) with a universal implicit constant, where
L is the binary size of the nuclear list. This remains a very large
exponential bound, without a claim of novelty or practical efficiency.

## Actual finite molecular certificates

All distances below are in atomic units, with infinite-mass fixed nuclei.
All runs used the full K=2 spatial cube and both spins: N=1 therefore has
16 occupation states. M=8, R=1; the box is (-2,2)^3. The pair integration
grid is unused because N=1. No external energy digits entered any computation.

| Nuclear centers and charges | Nuclear grid | Bits | Electronic interval | Seconds | Peak RSS bytes |
|---|---:|---:|---|---:|---:|
| H2+: charge 1 at (-1,0,0) and (1,0,0) |12|24|[-2,-3012999/8388608]|11.691624|27033600|
| Same H2+ input, refined grid |24|28|[-2,-68998015/134217728]|91.504502|27115520|
| HeH: charge 2 at (-1,0,0), charge 1 at (1,0,0) |12|24|[-9/2,-8400385/8388608]|12.590769|27131904|

These are the files `H2plus_N1_K2_Jn12_v1.json`,
`H2plus_N1_K2_Jn24_v1.json`, and `HeH_N1_K2_Jn12_v1.json`.
Each contains its complete interval matrix, physical nuclei, spin occupations,
clipping and complement scalars, source hashes and environment metadata.
All have 72 nuclear-integral cache entries and no pair-integral entries.
The symmetric H2+ midpoint matrices have no off-diagonal couplings within
this parity-limited K=2 cube, hence need zero bisections. The asymmetric HeH
matrix has nonzero couplings and used nine rational PSD decisions. No
special origin-parity cancellation was incorrectly applied to its nuclei.

The conservative lower endpoint still comes from the general hydrogenic
floor; these outputs demonstrate the molecular computation path, not sharp
physical ground energies. Grid refinement improved the H2+ variational upper
bound. Its roughly eightfold elapsed-time increase is an observation of
cubic cell enumeration on this shared machine, not a proved timing law.

`molecular_total_from_stage_v1.py` constructed the total-energy records only
after a fresh complete recomputation of their electronic source certificates.
It adds the directed nuclear constant and records the source-certificate hash.
Its `check` command repeats both stages. The exact separations in these two
instances make the constants rational:

* H2+ has C_nn=1/2 and total interval
  **[-3/2,-1889151/134217728]** in `H2plus_total_from_stage_v1.json`.
* HeH has C_nn=1 and total interval
  **[-7/2,-11777/8388608]** in `HeH_total_from_stage_v1.json`.

No ionization or molecular dissociation threshold is used as an excited-state
separator. These broad total intervals do not establish molecular binding.

## Verification and discovered sharpness issue

Six molecular test groups passed:

1. Exact rational charges and canonical centers; rejection of floating-point
   nuclei, nonpositive charges and coincident centers.
2. An off-center (111,211) integral is strictly negative at center (1/2,0,0),
   and its reflected-center value is its exact negative interval. This is
   a direct regression against an invalid origin-parity shortcut. Even-parity
   origin entries agree with the existing reflected kernel.
3. The one-origin-nucleus matrices contain the specialized atomic intervals
   in all 120-by-120 N=2,K=2 positions, and have identical basis/kinetic data.
4. Every one of 120-by-120 entries for a constant clipped two-center potential
   with total rational charge 5/2 contains the exact kinetic-minus-attraction-
   plus-repulsion matrix. This exercises electron repulsion and all spin
   occupations along with rational nuclear charges.
5. Rational and irrational nuclear-separation constants, including exact
   squared-bound checks at separation sqrt(2); vacuum total certificates
   replay, and a tampered total endpoint is rejected.
6. Eighty-one exact IMS radius/tail/width budget cases pass.

An initial test incorrectly demanded identical interval widths between the
specialized origin kernel and the generic full-cube kernel. The latter is
correctly wider at exact parity zeros because it retains cell uncertainty.
The test was corrected to require containment of the sharper atomic bounds.
No physical matrix or continuum theorem was changed to accommodate that
overstrong test expectation.

`verify_molecular_v1.py` copied the required sources and the first H2+
certificate into a new temporary directory, ran Python `-I -B`, compiled
all copied sources, ran all six test groups, fully recomputed the positive-N
certificate, generated/checked vacuum box/electronic/total certificates,
and rejected a changed nuclear coordinate. All five subprocesses exited 0.
The receipt `isolated_molecular_rebuild_result_v1.json` records source hashes,
commands and outputs; elapsed time was 30.594615 seconds. No bytecode or
third-party/disk cache was used; in-process arithmetic memoization was used.
This is isolated source reproducibility of this computational branch.

The separate total-energy checker was also replayed from copied sources
with `-I -B`, including a complete asymmetric HeH electronic stage
recomputation. `isolated_molecular_total_replay_v1.json` records PASS in
11.652075 seconds and the exact total interval [-7/2,-11777/8388608].

`check_uniform_molecular_sizes_v1.py` additionally passed 63 exact level-plan
regressions, including fractional charges, nonintegral centers and widely
separated/high-charge nuclei. These checks exercise the displayed explicit
size bounds; the universal bit theorem depends on its paper argument.

The independent root reviews inspect the exact molecular and bit-size
arguments. Agreement and finite tests do not replace proof. The molecular
translation/form bridge remains paper mathematics and the certificate
checker shares the Python arithmetic implementation. The separate atomic
formalization progress does not silently verify this new molecular model.

## Continuation frontier

The requested finite rational molecular energy class now has a concrete
paper-supported computability construction and explicit uniform exponential
cost analysis. Remaining work includes a formal molecular realization and
integral/algorithm correctness bridge, practically useful lower estimates,
and efficient approximation improvements. Wavefunctions, observables,
excited states and time evolution need separately stated and proved output
theorems; none follows from this energy interval alone.

All prior sealed work and frozen files remain unchanged. New molecular
sources and outputs are confined to this continuation directory; the exact
baseline provenance is listed in the companion proof.
