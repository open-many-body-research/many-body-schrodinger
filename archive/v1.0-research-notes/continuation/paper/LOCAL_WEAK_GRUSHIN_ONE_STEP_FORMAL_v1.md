> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual local weak Grushin one-step gain

Let Y=R⁴, T=R^m for any finite coordinate index set (including m=0), and c>0. Work on the ordinary product with product Lebesgue measure and complex L². Define the actual principal operator P_c=−Δ_y−c|y|²Δ_t by compact smooth weak tests.

For every open Ω and real smooth compact cutoff χ with support contained in Ω, there exists C≥0, selected before the functions, such that any actual L² classes G,h satisfying P_cG=h against every real smooth compact test in Ω admit an actual L² class U=χG almost everywhere and genuine weak first Y/T and ordered second YY derivatives. Put F=C‖G‖² and M=C(‖G‖²+‖h‖²). The proved estimates are

- Σᵢ‖D_yᵢU‖² ≤ 2F+3M/4.
- Σⱼ‖D_tⱼU‖² ≤ M/(16c).
- ΣᵢΣⱼ‖D_yⱼD_yᵢU‖² ≤ 3M/2.

All weak derivatives are actual complex L² witnesses tested against every real C∞ compact function on the full product. The ordered YY derivatives act on the same first-Y family. No derivative, Sobolev regularity, gap, eigenfunction, or approximation sequence of G is an input hypothesis.

The proof fixes an intermediate compact set and open neighborhood of supportχ inside Ω. Actual partial mollification only in T has norm contractions and strong product-L² convergence, with one eventual threshold for all tests on this fixed interior domain. Genuine T derivatives of the mollified function supply the full ordinary Laplacian equation; the previously proved two-cutoff ordinary elliptic bootstrap gives local weak H² at each sufficiently fine stage. These preliminary derivative bounds may depend on the stage and are never used as uniform bounds.

The proved local energy, plateau derivative comparison and exact weak cutoff commutator construct a compact actual weak H² function U_n=χG_n and genuine global L² output H_n=P_cU_n. A single constant, fixed before G,h, bounds ‖U_n‖² and ‖H_n‖² by the original input norms. The compact weak Grushin estimates and directional interpolation bound the three required derivative families. Multiplication by the fixed cutoff preserves the actual strong-L² limit even for arbitrary AE representatives and eventual-stage definitions. The anisotropic bounded weak-limit theorem constructs the limit witnesses and preserves the three constants; it does not assume derivative convergence or limit derivative existence.

The result is a fully formal mathematical local estimate. C is a finite analytic existence bound with explicit intermediate coefficient formulas, not yet a proved explicit function of geometric scale, nor an executable constant-computation routine. The displayed statement uses global L² G,h; a separate compact indicator-extension wrapper is being composed to give purely local L² data and local-integral bounds. No full joint H² assertion follows from one-step: TT and unweighted mixed derivatives are not part of this conclusion. The separate two-step bootstrap, scale-uniform analytic constants, factorial recurrence, descent and other collision strata remain open. No novelty or efficient numerical solver is claimed.

Two modules/four declarations passed complete expanded-statement and axiom audits 20260910T174604_254975Z and 20260910T175407_072502Z, only propext, Classical.choice and Quot.sound. The proof is kernel elaboration in Lean4.34.0-rc2 with pinned Mathlib d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9. Development dependency objects were reused. These final sources are outside the successful 743-target v19 source snapshot; their own isolated continuation rebuild remains to be performed. Failed unsealed draft elaborations are preserved and excluded from accepted evidence.

Frozen preservation anchor: rwa_proof/RWA_THEOREM.md SHA d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09, commit166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. Full original Theorem T remains UNVERIFIED. Next active work: purely local data and physical potential reduction; spectator weak differentiation and Leibniz; second gain to actual joint H².
