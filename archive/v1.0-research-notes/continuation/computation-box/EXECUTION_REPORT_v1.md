> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# One-electron execution checkpoint

The strongest executed statement in this branch is a paper-linked rational
enclosure for the actual N=1,Z=1 Dirichlet-box energy on `(-4,4)^3`, and hence
for the full-space energy:

`[-1/2, -275632905/1073741824]`.

Its exact width is `261238007/1073741824 < 1/4`. This is **exact-rational
execution with a paper-level continuum proof**, not a Lean-verified continuum
output. Its lower endpoint is the elementary hydrogen lower bound. The
Galerkin-complement/restoration formula was evaluated, but is weaker at these
small stages and does not improve the lower endpoint. No reference digits were
used to choose or validate either endpoint.

## Final source and concrete certificates

The final mathematical implementation is `exact_box_v1.py`, SHA-256
`f1358f9f63f025554128a20ad2d464934509a6363ae49bc028cba92e2673ad58`.
The following outputs match that exact source. All use Z=1,R=2,M=8,bits=32.

| Certificate | K | J | spatial dimension | time (s) | achieved box upper endpoint |
|---|---:|---:|---:|---:|---|
| `n1_Z1_R2_M8_K1_J64_v1.json` | 1 | 64 | 1 | 6.7794 | `-275632905/1073741824` |
| `n1_Z1_R2_M8_K2_J32_v1.json` | 2 | 32 | 8 | 4.0764 | `-7653401/33554432` |
| `n1_Z1_R2_M8_K3_J32_v1.json` | 3 | 32 | 27 | 36.0632 | `-7653401/33554432` |

The two full spin blocks are identical. Reported sizes count one spatial block.
The JSON files record exact matrix intervals, all scalar bounds, CPU environment
and peak resident memory. Timings are observations on this machine, with
independent runs sharing the machine; they are not certified complexity bounds.

K=3 produces a genuinely coupled compressed matrix and ten nontrivial rational
PSD bisection decisions. Its midpoint-matrix ground energy lies in
`[-1920869650855/4398046511104, -3835578177607/8796093022208]`, but the entry-error
row bound is approximately 0.491. Consequently its continuum upper bound uses
the included diagonal trial. This is a concrete conditioning/integration
limitation: increasing basis size without refining matrix integration did not
improve the certified answer. The midpoint-matrix digits are not physical
energy certificates.

## Verification performed

`test_exact_box_v1.py` passes ten grouped tests: rational interval containment,
directed dyadic rounding, rational square roots checked by exact squaring,
clipping branches, algebraic sine values, orthonormality of integrated sine
products, degenerate PSD pivots, all 729 small symmetric 2-by-2 cases, known
finite-matrix eigenvalues, a constant-potential continuum matrix, and scalar
schedule budgets. These are meaningful finite tests, not general proofs.

The independent continuum reviewer checked all 15,625 symmetric 3-by-3 matrices
with entries in {-2,-1,0,1,2} against the all-principal-minors PSD criterion. They
also checked K=3,J=3 in a provably constant potential, including 98 same-parity
offdiagonal positions; receipt `independent_review_checks_v1.json`. This catches
cases beyond the implementation's own tests. Their formula review checked the
unclipped-minimizer restoration argument, exact omitted-mode threshold,
parity/reflection reduction, and strict requested-width convergence margin.
Agreement is corroborating review, not a substitute for mathematical proofs.

The `check_n1_*.json` receipts independently execute the published checker in
fresh processes, recomputing every interval matrix entry and all scalar bounds.
They share the published arithmetic implementation and its trust boundary.

`isolated_rebuild_result_v1.json` records **PASS** for a source-only rebuild:
three source files and the final K1/J64 certificate were copied to a fresh
temporary directory. Python `-I -B` compiled the copied sources, ran the tests,
regenerated the certificate, and checked both original and regenerated copies.
Every exact mathematical field reproduced. No external package, user-site
module, numerical disk cache, or bytecode cache was used. The only cache use is
in-process memoization of pi, sine and overlap interval evaluations.

## Limitations and next obligation

The schedule file `n1_requested_half_schedule_v1.json` exposes an infeasible
requested-width construction: at width 1/2 it already requests over 4 trillion
spatial basis states and over 10^63 grid cells. That schedule was inspected, not
executed. The feasible explicit-stage outputs above do not establish practical
arbitrary-precision computation or a fully verified implementation theorem.

The source and paper contract provide an N=1 specialization of `BoxEnclose`;
all N>=2 determinant, pair-interaction, clipping-sign and full fermionic
obligations remain open in that routine. The next active computation is a
separately versioned N=2 opposite-spin one-determinant certificate with actual
pair-Coulomb interval integration. It does not implement the frozen Theorem T
dictionary or its claimed rate/complexity.

For the detailed proof, provenance and commands see `BOX_SOLVER_v1.md`. This
checkpoint does not claim novelty or closure of F02/F03/F04 or full Theorem T.
