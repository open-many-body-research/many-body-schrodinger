> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual polynomial series and complex analyticity

Evidence: fully formalized conditional polynomial-series theorems. This
checkpoint does not yet identify the polynomial inputs with the Taylor
pieces of the physical KS lift.

Let sigma be any finite variable type and let A_n be actual complex
MvPolynomials homogeneous of degree n. Define L1(P) as the finite sum of
absolute values of P's actual coefficients. If M,D are nonnegative and
L1(A_n) <= M D^n, the literal sum of polynomial evaluations is complex
analytic on D ||X||_infinity < 1. For every r >= 0 with Dr < 1, the series
converges absolutely and uniformly on the closed complex polydisc of radius
r, and its sum has norm at most M/(1-Dr).

For Q_n homogeneous of degree n with L1(Q_n) <= M D^(n+1), the corresponding
bound is MD/(1-Dr). This is the odd radial family indexed from its actual
degree zero. A separate theorem explicitly restores an original family B_m
with B_0=0, including original range partial sums and the equality of its
sum to the shifted sum. Thus the possibly nonzero constant B_1 is retained.

The analytic proof constructs a continuous n-linear map from each actual
homogeneous polynomial, with diagonal evaluation equal to that polynomial
and operator norm bounded by its literal L1 coefficient sum. This follows
from an exact finite word for every exponent multiset and the product of
coordinate projections. The coefficient maps form an actual
FormalMultilinearSeries. Its sum equals the polynomial sum term by term;
the geometric coefficient bound proves its radius, and Mathlib's generic
FormalMultilinearSeries.analyticOnNhd applies to the multivariable domain.
The D=0 case has its own proof and gives analyticity everywhere. No
univariate-only uniform-limit theorem is used.

The representation uses classical selection and does not claim an
executable rational conversion or energy algorithm. All declarations were
compiled using the pinned Lean/Mathlib development caches and checked by
the strict v8 exact-statement and transitive-axiom audit. Only propext,
Classical.choice and Quot.sound occur. This does not constitute a source
dependency rebuild or change the recorded isolated rebuild status.

The current implementation subsequently composes these results with the
literal finite KS descent on a specified real-coordinate homogeneous
polynomial family. Physical Taylor extraction, spectators, circle
invariance inherited from the actual function, analytic uniqueness and the
remaining Theorem T approximation chain are separate obligations.

Frozen provenance: rwa_proof/THEOREM_T_COMPOSITION.md, SHA256
1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da;
commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660;
tag theorem-t-proof-freeze-2026-09-09. All artifacts in this checkpoint are
new continuation files; frozen and previously successful source bytes are
preserved.
