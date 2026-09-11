> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit nested weak derivative norm bounds

Let f,d,h,e be actual complex L² classes on the ordinary product of arbitrary finite-dimensional real inner-product spaces. For a fixed product direction v, assume genuine compact-test weak equations Dᵥf=d and Dᵥh=e. Let η be real smooth compactly supported, with h=θd almost everywhere and θ=1 on the topological support of η. No derivative, boundedness, or continuity of θ is assumed, and no global weak derivative of d is assumed.

Suppose the actual cutoff satisfies |η|≤M, |Dᵥη|≤A, and |Dᵥ²η|≤D everywhere. The new theorem constructs genuine weak derivative outputs U,a,b and proves both the exact almost-everywhere formulas

\[
U=\eta f,\quad a=\eta d+(D_v\eta)f,\quad
b=\eta e+2(D_v\eta)d+(D_v^2\eta)f
\]

and the triangle norm bounds

\[
\|U\|_2\le M\|f\|_2,\qquad
\|a\|_2\le M\|d\|_2+A\|f\|_2,
\]
\[
\|b\|_2\le M\|e\|_2+2A\|d\|_2+D\|f\|_2.
\]

The same exact formula and genuine weak-derivative conclusions are provided with squared bounds

\[
\|U\|_2^2\le M^2\|f\|_2^2,
\]
\[
\|a\|_2^2\le2(M^2\|d\|_2^2+A^2\|f\|_2^2),
\]
\[
\|b\|_2^2\le3(M^2\|e\|_2^2+4A^2\|d\|_2^2+D^2\|f\|_2^2).
\]

The proof reuses the exact nested-cutoff calculus theorem. The norm argument identifies each actual output with actual bounded L² multiplier objects and applies the triangle inequality. Smooth compact support proves all coefficient multipliers are bounded in the required measure-theoretic sense. Three new generic helpers also apply to arbitrary measures and to actual L² outputs equal almost everywhere to one, two, or three bounded real weighted inputs.

Source modules are `LpRealWeightedSumNorm_v1`, `ProductNestedWeakSecondNorm_v1`, and `ProductNestedWeakSecondSquared_v1`. Exact source/object hashes and strict expanded-statement/axiom receipts are recorded in `audits/PRODUCT_NESTED_WEAK_SECOND_NORM_CHECKPOINT_v1.json`. The full axiom dependencies contain only standard foundations. Pinned library and project object caches were reused; these modules postdate the completed v18 isolated source-rebuild snapshot.

This supplies explicit constants for the nested second-derivative step used in the quantitative joint H² argument. It does not prove the full two-step Grushin estimate by itself, an analytic approximation rate, an executable solver, or full Theorem T. No automatic computation of the cutoff bounds is claimed.

Frozen artifacts remain unchanged: original `RWA_REPORT.md` SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, freeze `THEOREM_T_FREEZE_2026-09-09_212604`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.
