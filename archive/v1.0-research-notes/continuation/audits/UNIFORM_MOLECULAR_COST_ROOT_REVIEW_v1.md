> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Root review of the uniform molecular bit bound

Reviewed source: `../computation/box/UNIFORM_MOLECULAR_SIZE_BOUND_v1.md`, SHA-256
`8b5ec60dd229d9ca7b8457f01005edeb339382b74b72a43f49f1ffa7779f1aa1`.
This is a paper complexity proof about the implemented rational algorithm. It is not a Lean program-correctness or cost theorem.

The claimed scope is finite distinct rational nuclear centers, positive rational charges, integer N>=0 and p>=1, and nuclear binary input length L. The resulting upper bound is 2^O((N+1)(p+N+L+1)), with a universal implicit constant in a schoolbook bit model. It covers construction, output and fresh replay. It is exponential in requested precision and is not a claim of uniform efficient many-body computation.

I checked the value and representation bounds for charge sum, center radius and nonzero nuclear separations. The input-length argument charges products of all supplied denominators only once where a common denominator is available. It separately charges unrelated denominators in nuclear repulsion. N=0 is explicitly included: the factor N+1 is necessary because input parsing and nuclear repulsion still cost work.

The original displayed cutoff calculation lacked enough explicit slack if read solely through B<=2^(11S). The final proof now supplies B<=256N^6Q^4t<=2^(9S), deriving rhs<=12*2^(29S)<=2^(30S)<=2^(34S) using S>=4. This repairs the displayed inference without changing the algorithm. The subsequent K, occupation dimension, local grid, rounding precision and PSD decision bounds have sufficient slack, including ceilings. Local LCMs contain at most twelve indices, so a hidden global LCM exponential is absent.

The complexity proof charges quadrature and occupation loops, linear cache searches, repeated precision stages, serialization, and all rational operands. The matrix entries have a common denominator after outward rounding. Schur operands are bounded as ratios of minors using Hadamard bounds, yielding O(m(b+q+log m+L)) bits. They are not counted as unit-cost arithmetic. Every size and operand bound is at most exponential in NS for N>0; composing polynomial-cost primitives preserves the asserted universal exponential bound.

No remaining error was found in this cost derivation. Its validity remains conditional on the separately reviewed paper continuum/box/rounding correctness arguments and the declared runtime model. It does not establish a new complexity lower bound or literature novelty. The concrete conservative positive-N requested-width schedules have not been run; the recorded finite-stage enclosures and replays are the actual executions.

The completed molecular seal remains untouched. This is a new supplementary review of its exact final proof. Historical origin: frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.
