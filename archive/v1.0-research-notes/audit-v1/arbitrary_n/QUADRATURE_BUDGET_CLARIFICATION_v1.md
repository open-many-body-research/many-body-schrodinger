> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit entry-error allocation for the bounded-box specification

Date: 2026-09-09. This is an append-only clarification of the sealed post-freeze file `GAP_FREE_COMPUTABILITY_v1.md`, SHA-256 `18093804ba5070c6ad66767432de1ee04eb76bec52bdbe13ee3e0dfc65f4b1bb`, §5, step 3 and the paragraph following equation (23). That file remains unchanged. The underlying frozen provenance is commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.

The original specification reserves half of the entry-error budget for potential quadrature and describes the remaining half for midpoint evaluation, without separately allocating the kinetic diagonal's π² evaluation. To make the stated full-matrix bound unambiguous, use the following allocation. With e=ε/32, dimension m, and total absolute entry-error budget t=e/m:

| Contribution to one compressed matrix entry | Absolute error budget |
|---|---:|
| Clipped-potential midpoint quadrature, including all spin assignments | t/2 |
| All numerical evaluations and summation of that finite midpoint formula | t/4 |
| Kinetic diagonal evaluation, including its rational coefficient multiplying π² | t/4 |

Choose the grid using equation (23) to ensure the first bound. Refine the rational interval evaluations of potential, sine factors, determinants and their finite weighted sum until its interval width is at most t/2; taking its rational midpoint gives error at most t/4. Use exact rational arithmetic for the interval operations, or include any implemented outward-rounding errors in this same bound.

The kinetic matrix is diagonal in the specified orthonormal sine-Slater basis. For a diagonal entry aπ² with explicit positive rational a, compute a rational π² enclosure of width at most t/(2a), multiply by a exactly, and take the rational midpoint. Its absolute error is at most t/4. Kinetic off-diagonal entries are exactly zero and consume none of that allocation.

Compute each unordered matrix pair once and copy it to the symmetric position. Summing the three errors gives at most t=e/m for every entry of the full rational symmetric matrix A. Thus the existing operator error bound `||A−P(T+V_M)P||≤e`, the `BoxEnclose` width bound `9ε/16`, and the recursive enclosure budget are unchanged. A uniform three-way split would also work; the displayed half/quarter/quarter split preserves the original quadrature allocation.

This closes a specification detail identified by the independent spectral-computation review. It supplies no implementation, numerical atomic output, Lean theorem, or improved complexity claim. The end-to-end executable statement remains conditional on implementing and verifying `BoxEnclose` and its interval arithmetic.
