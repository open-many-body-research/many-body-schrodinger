> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# General finite matrices and requested-precision program checkpoint

This checkpoint supplies actual source for the complete finite fermionic
occupation matrix, requested-width BoxEnclose, and gap-free full-space atomic
wrapper. Root review found no defect in the stated paper composition. It does
not supply Lean implementation verification or a practical arbitrary-precision
atom calculation. All new sources and proofs have versioned paths; frozen
artifacts and earlier successful stages remain unchanged.

## Actual nonzero-particle execution

The complete N=2,K=2 sine-spin basis has 16 one-particle spin orbitals and 120
two-particle occupations. Every 120-by-120 matrix entry is computed, including
spin/exterior signs and all permitted offdiagonal terms. Z=2,R=1,M=8,bits=24:

| Source certificate | nuclear J | pair J | time (s) | full-space interval |
|---|---:|---:|---:|---|
| `occupation_N2_K2_M8_Jn16_Jp8_v1.json` | 16 | 8 | 14.2220 | `[-4,0]` |
| `occupation_N2_K2_M8_Jn32_Jp16_v1.json` | 32 | 16 | 84.3259 | `[-4,-13390107/33554432]` |

The second run used 10 exact rational PSD decisions; its exact width is
`120827621/33554432`. Both runs evaluated 36 canonical nuclear integrals and 666
canonical pair integrals (including exact parity-zero cases), with peak resident
memory 28,426,240 and 28,524,544 bytes. Both full replay receipts pass. These
remain broad bounds whose lower endpoint is the independent-hydrogen estimate;
they are implementation evidence, not improved physical accuracy.

`permutation_determinant_audit_result_v1.json` records exact agreement of all
765 independently expanded normalized determinant matrix elements. No creation/
annihilation routine or Slater-Condon formula is used in that reference.
Separate tests check canonical anticommutation on all 64 capacity-six Fock
states and 36 index pairs, and all 14,400 entries of a constant-potential
120-by-120 physical matrix. `isolated_occupation_rebuild_result_v1.json` records
PASS for copied-source compilation, these tests, independent permutation audit,
full stage regeneration, and checks of original and regenerated stage data.

## Implemented scheduled program, with exact execution boundary

`GENERAL_BOX_REQUESTED_WIDTH_v1.md` proves the stated requested-width box
algorithm on paper, using fixed clipping/cube/grid choices and a strict spatial
error margin followed by arithmetic-bit refinement. `ATOMIC_REQUESTED_PRECISION_v1.md`
composes it with the earlier fermionic gap-free localization argument, without
assuming a full-space minimizer, binding or gap. The wrapper is iterative to
avoid recursion-depth limits. The resulting requested-width procedures have
not been executed at positive N because their schedules are prohibitive.

The newly chosen common anchor reduces the N=1,Z=1,R=2,epsilon=1/2 scalar plan
to M=94,K=1418, but the dimension is still 5,702,413,264 and the minimum spatial
grid is 103,191,600,334,241,792 before node alignment. This is a schedule receipt,
not an emitted energy interval.

The scalar tests cover 144 box budgets, node alignment, 702 localization-level
budgets, and 729 minimum-interval width cases. Actual scheduled vacuum outputs
are checked, including extreme finite decimal inputs. `isolated_general_program_rebuild_result_v1.json`
records PASS for source-only compilation, tests, both vacuum certificate
replays, and rejection of a tampered energy. No positive-N scheduled execution
is hidden in that wording. All checkers share the published implementation;
no Lean/kernel correctness is inferred from these finite tests.

## Discovered runtime defect and repaired entry point

The earlier sealed N1 script's default Python environment rejects conversion
of integers exceeding 4300 decimal digits. A finite schedule input epsilon=10^-5000
reproduces the ValueError. The append-only issue
`ERRATUM_INTEGER_CONVERSION_LIMIT_v1.md` names the affected exact source/hash and
exception witness. The new `exact_integer_runtime_v1.py` policy is imported
before parsing and serialization; the same call now produces 227823 JSON
characters and roundtrips exactly. Earlier finite certificates are unaffected.
This corrects a concrete implementation claim rather than editing its history.

## An explicit cost obstruction in this version

The global common node grid uses `L=lcm(1,...,K)`, forcing J>=L. For every
binomial coefficient binom(K,j), each prime valuation is at most the number of
powers of that prime <=K: the factorial-valuation difference contributes zero
or one at each power. Therefore each binomial coefficient divides L. Since
their K+1-term sum is 2^K,

`L >= max_j binom(K,j) >= 2^K/(K+1)`.

Thus this version's global node alignment alone costs exponentially many cells
in K. In the full-space schedule for fixed positive N,Z, R grows as 2^p,
M grows at least as 2^p and eta is proportional to 2^-p; the complement choice
forces K at least a constant times 2^(5p/2). Consequently the required global
grid has doubly exponential growth in p. This is a decisive obstruction to
presenting this particular realized schedule as polynomial or merely singly
exponential precision cost. Integer/operand costs add further work.

The next version will resolve each cached integral's own orbital nodes. A
nuclear entry involves only six scalar indices and a pair entry only twelve,
so their LCMs are at most K^6 and K^12. Every local grid can be at least the
same certified minimum while remaining below that minimum plus its local LCM.
This removes the global exponential-in-K node alignment without changing the
physical orbital space or the fixed-grid error proof. It requires new source,
tests and a versioned contract; the present sealed implementation stays intact.
