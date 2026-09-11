> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Formal semantic supplement 001 — complex Hardy and weak cutoffs

This completed supplement updates `FORMAL_SEMANTIC_REVIEW_v2.md`, SHA-256 `19f9ca0823a8b2e072978b1acc8cc1efc9eb1e17b89451be2c4962de30117364`. It records results completed after that review's accepted source set was fixed. The original review remains unchanged.

## Newly accepted results

**Complex compact C¹ Hardy is now fully formalized.** For every `u : EuclideanSpace ℝ (Fin 3) → ℂ` with `ContDiff ℝ 1 u` and `HasCompactSupport u`, the exact final statements prove

- actual Lebesgue integrability of `‖u x‖² / ‖x‖²`;
- `∫ ‖u x‖²/‖x‖² ≤ 4 ∫ Σᵢ ‖fderiv ℝ u x (EuclideanSpace.single i 1)‖²`;
- `MemLp (fun x => u x / (‖x‖ : ℂ)) 2 volume`, together with the corresponding squared-norm integral bound.

The declarations `TheoremT.HardyAudit.complex_hardy_expanded` and `complex_multiplier_expanded` expose the Euclidean space, volume measure, complex codomain and coordinate vectors directly. They do not rely on a project abbreviation hiding another domain or measure. There is no regularized-estimate or integrability premise in these final statements.

`HardyLimitComplex_v1` splits u into real and imaginary parts, applies the already proved real theorem, and proves that real differentiation commutes with both projections. The squared complex norm is the sum of the squared real components; no extra factor or holomorphic hypothesis is introduced. All sums and integral additions have the required integrability proofs. `HardyLimitComplexL2_v1` obtains actual L² membership from integrability of the squared norm and measurability of the quotient; the conclusion is not inferred from a totalized Bochner integral alone.

This supersedes the original review's pending **complex compact-function extension** frontier. Extension to the project's arbitrary distributional weak H¹ space is still not proved by these files.

**Smooth compact cutoffs preserve the actual weak H¹ and H² domains.** `HardyWeakCutoff_v1` defines multiplication of an L² equivalence class by a continuous compactly supported real cutoff and proves its expected almost-everywhere representative. For a smooth compact cutoff χ, `weakPartial_cutoff` proves the correct derivative `χg + (∂ₖχ)f` whenever `WeakPartial f g k`. `HasH1.cutoff` assembles all first derivatives. `HardyWeakCutoff_v2.HasH2.cutoff` supplies all mixed second derivatives by applying the H¹ product result to the actual first-derivative witnesses and to derivatives of χ.

The cutoff theorem assumes χ is smooth, not f. Its use of the test function φχ is legitimate because both factors are smooth and the product has compact support. Boundedness of the cutoff and its compactly supported derivatives supplies the required actual L² products.

These are scalar domain-preservation results. An arbitrary cutoff need not preserve fermionic antisymmetry; that requires permutation invariance of χ or subsequent antisymmetrization. No sequence χ_R, convergence to one, derivative-norm approximation, Sobolev density, Hamiltonian graph core, or continuum spectral result is claimed here.

## Evidence

Independent expanded-statement and axiom audits both exited zero:

- `formal_semantics/20260909T231031_400350Z/receipt.json`: four final public complex-Hardy declarations, including the alias-free statements.
- `formal_semantics/20260909T231220_386190Z/receipt.json`: six cutoff declarations, including the multiplier definition.

All ten requested axiom outputs appeared. Every audited source and object remained unchanged during its audit. Recursive dependencies contain only the accepted foundational axioms `propext`, `Classical.choice`, and `Quot.sound`. Private complex-calculus helpers are included in those recursive dependency checks. No forbidden source token was detected. The compiler, object-cache disclosure and display settings are the same as in the original review. Exact source/object and receipt hashes are recorded in `FORMAL_SEMANTIC_SUPPLEMENT_001_MANIFEST_v2.json`.

The historical frozen path, SHA-256, commit and tag, and the exact prior physical-definition hashes remain those cited in the supplemented review. This update changes no physical definition and modifies no frozen or completed prior artifact. F02 still needs weak-Sobolev extension, configuration slicing, quantitative Coulomb and relative-Laplacian bounds. F03, F04 and full Theorem T remain unverified by this accepted source set.
