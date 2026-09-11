> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent review of the weak KS removability argument

Evidence category: mathematical paper review, not formal verification.

Reviewed final artifact: `KS_WEAK_REMOVABILITY_v1.md`, SHA-256
`ba8769955d76e01ce561a68071ad5832828106c3ca614ea8fe1e19c36aa78cde`.

The root agent read the complete proof and checked the test convention,
all cutoff commutator terms, annulus and ball volumes, the constants in
(K6) and (K10), and the use of vanishing local L2 mass. The pairing is
bilinear and uses the distributional transpose; the potential therefore
appears without conjugation. The C2 cutoff test is licensed by H2
approximation supported away from the collision and the outer boundary.
No derivative or trace of the unknown solution is assumed at the removed
stratum. The counterexamples explaining the transverse dimension and L2
threshold are consistent with their stated fundamental-solution fluxes.

The explicit nuclear and electron-pair coordinate changes give the stated
kinetic coefficients c=4 and c=1. The cancellation of the Coulomb term,
both scaled potentials, the two displacement bounds, and the equation for
the scaled difference have the correct signs and factors. The local weak
elliptic bootstrap is used only to justify the classical chain rule away
from collisions; it supplies no uniform analytic estimate in this result.

Before sealing, review requested an explicit parameter range 0<epsilon<=
epsilon0 and a common physical Lipschitz neighborhood containing all
scaled chart images. The final source states these restrictions and keeps
spectator separation explicit. No mathematical change to a frozen or
previously sealed artifact resulted.

Accepted result: an actual L2 weak solution off a codimension-four KS
stratum satisfies the same Grushin equation across it. Under the stated
physical Lipschitz input and separated chart, this applies to the actual
KS pullback and supplies the distributional premise for the separately
proved initialization and factorial recurrence. It does not construct a
physical eigenfunction, prove quantitative distance descent, establish
boundary compatibility, or verify full Theorem T.

Frozen provenance is recorded in the reviewed artifact: commit
166f43f2f0178f92d8c4d1dde209ef0eeaefa660, annotated tag
theorem-t-proof-freeze-2026-09-09, and exact frozen source hashes.
