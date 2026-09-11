> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent review of the local-grid operational bit bound

Evidence: paper proof and source inspection, not formal implementation verification.

Reviewed `LOCAL_GRID_AND_BIT_COST_v2.md`, final SHA-256
`934358a4952d3408aa67945d9c0ece539e8b1e403e93e86465adac708c9ecf79`.
The root independently read the full argument and inspected the actual
Machin, sine, square-root, clipping, overlap, signed cell grouping,
occupation assembly, rational PSD, and bisection implementations.

The per-integral LCM resolves all relevant sine nodes while avoiding the
global LCM. The arithmetic endpoint-excess bound is conservative and
separates cell variation from rounding error. The precision threshold has
strict acceptance margin. The fixed dyadic denominators through nuclear
and pair sums, the final common matrix denominator, and minor/Hadamard
bounds for Schur updates address operand growth. The declared cost model
charges integer operations and even worst-case linear table lookup.

Review requested an additional squared-log overhead for precision attempts
and caches retained across those attempts. The final text includes it;
the fixed-N,Z singly exponential precision conclusion is unaffected.
The displayed atomic schedule exponents, sufficient precision, and PSD
bisection count give 2^O_(N,Z)(p) in the declared binary integer model.
This is not polynomial in p or in the binary input length log p, nor a
claim of uniform efficiency in N and Z. No positive-N theoretical schedule
has been executed. Finite-stage outputs and replay evidence are separately
recorded; correctness relies on the specified paper continuum and
localization arguments and the disclosed Python arithmetic runtime.

This is a separately identified gap-free method, not verification of the
frozen trial dictionary, rate 1/16, complexity exponent 2256, or full
Theorem T. Historical hashes and new source versions are listed in the
reviewed artifact; no sealed predecessor was changed.
