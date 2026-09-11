> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Independent formal semantic review — continuation v2

**Completed checkpoint.** The reviewed final Lean sources faithfully represent the stated continuum objects. Their compiled results establish collision nullity, exact permutation covariance, the full graph/domain characterization with an explicit Coulomb-multiplier condition, the real three-dimensional Hardy inequality for compactly supported C¹ functions, and inclusion of compactly supported complex C² functions in the actual weak H² domain. The remaining multiplier, self-adjointness and spectral obligations are not silently discharged.

This review concerns new work only. It did not repeat the broad frozen-project audit or reassess unrelated analytic, numerical or complexity claims.

## Exact results and evidence categories

1. **Collision geometry — fully formalized.** `CollisionNull_v2` proves nuclear and pair collision sets Lebesgue-null for every finite electron count, including the vacuous N=0 case. Almost every configuration is collision-free. The actual totalized Coulomb potential is measurable everywhere and continuous off collisions. Changing the potential only at collisions preserves multiplication almost everywhere and the specified scalar weak graph. None of these statements asserts that multiplication sends H² into L².

2. **Weak Sobolev algebra and coordinate covariance — fully formalized.** `WeakDomainAlgebra_v2` proves complex linearity of actual distributional partial derivatives and forms the actual weak H² and fermionic H² submodules. `WeakPermutation_v2` proves weak-derivative covariance, then H¹/H² preservation, without replacing weak derivatives by classical derivatives or requiring a smooth input. For the project's convention `(Pπ x)i = x(π i)`, a derivative at original coordinate k becomes a derivative at π(k) after pullback; output witnesses at k correctly use π⁻¹(k). This convention was checked for general permutations, not just transpositions.

3. **Potential covariance — fully formalized, with a conditional product consequence.** `PotentialPermutation_v2` proves the exact original potential invariant under all electron permutations. Reindexing the i<j pair sum is justified by a symmetric zero-diagonal kernel counting identity; no order preservation is assumed. The potential term preserves simultaneous spin-space fermionic symmetry whenever its componentwise L² product representatives exist. That last premise is visible and does not assume output antisymmetry.

4. **Actual full Coulomb graph — exact formal characterization.** `FermionicGraphAssembly_v2.hamiltonian_graph_existsUnique_iff` states, for the unchanged graph and every real charge Z,

   `∃! h, hamiltonianGraph N Z ψ h` if and only if
   `ψ ∈ targetDomain N ∧ ∀ σ, CoulombProductL2 Z (ψ σ)`.

   Here `CoulombProductL2` is literally `MemLp (fun x => (coulombPotential N Z x : ℂ) * f x) 2 volume`. It is not an abstract field asserting the desired operator theorem. Scalar graph covariance and scalar uniqueness prove that every componentwise graph output of a fermionic input is itself fermionic. Output symmetry is therefore discharged, rather than inserted as a hypothesis of the existence theorem. The existence implication remains conditional on the genuine multiplier fact.

5. **Partial linear operator — fully formalized with its actual limited domain.** `CoulombOperatorCore_v2` turns the linear, single-valued concrete graph into a `LinearPMap`. The equality of its graph to the intended relation is proved. Mathlib's graph-to-partial-map construction has a zero-map fallback for a nonsingle-valued relation; the proved single-valuedness and graph equality rule out reliance on that fallback here. The later `coulombPartialOperator_domain_iff_H2_multiplier` identifies its domain exactly as fermionic spinors whose components are weak H² and whose Coulomb products lie in L². It does not identify that domain with all fermionic H² inputs. Classical choice selects the unique mathematical value; this is not an executable energy solver.

6. **Classical three-dimensional Hardy inequality — fully formalized.** `HardyLimitComposition_v1` proves, for every real C¹ compactly supported function u on `EuclideanSpace ℝ (Fin 3)`, both actual integrability of u²/‖x‖² and

   ∫ u²/‖x‖² ≤ 4 ∫ Σᵢ (Du[eᵢ])².

   It separately proves `MemLp (fun x => u x / ‖x‖) 2 volume` with the same bound. The real C¹ compact support hypotheses are the only mathematical hypotheses of the final composition. The all-δ regularized estimate that appears as a premise in the intermediate limit bridges has been discharged by `HardyRegularized_v3.regularized_hardy_integral`.

7. **Classical-to-weak domain bridge — fully formalized.** `HardyWeakCore_v1.compact_c2_in_weakH2` proves that any complex-valued compactly supported C² function on the original `Configuration N` represents an element of the original `HasH2` domain, for every N. The result includes all mixed second weak L² derivatives. The auxiliary `MemLp` premise in `compact_c2_hasH2` is supplied in this final theorem. It does not prove density in a Sobolev norm.

## Fidelity and adversarial checks

The imported spatial space is the actual Lebesgue L² quotient on `EuclideanSpace ℝ (Fin N × Fin 3)`. The spin space is the finite ℓ² sum over all maps `Fin N → Fin 2`. Antisymmetry simultaneously transforms spatial coordinates and spin labels: the representative equation is ψ(Pπx, σ∘π) = sign(π)ψ(x,σ). No spin sector or finite spatial discretization replaces that space.

The weak derivative definition tests against every real smooth compactly supported test function and integrates complex vector values. Real tests determine both real and imaginary distribution components. L² local integrability and compact supports justify the integrals, so the totalized Bochner integral is not exploited to make the distributional condition vacuous. `HasH2` explicitly requires all first derivatives and all mixed second derivatives in L². The kinetic term is exactly minus one half the sum of diagonal second derivatives. The nuclear attraction and positive pair repulsion retain their original signs and distances.

For Hardy, the completed-squares identity was checked independently. With q=‖x‖²+δ and Bδ=x/q,

`(4 Σᵢ(∂ᵢu)² + 2 div(u²Bδ) − u²/q) q²`
`= Σᵢ(2q∂ᵢu + uxᵢ)² + 5δu²`.

The coefficient 5 is correct. Compact support makes the divergence integral zero and all regularized quantities integrable. The Fatou bridge proves integrability of the singular limit as well as its inequality; it does not merely compare a possibly totalized real integral. The origin is excluded only on a null set. Thus the final classical Hardy statement is stronger than a helper derivative formula and weaker than the still-needed arbitrary weak-H¹ theorem.

No hidden equivalent of the missing multiplier theorem, dense-domain theorem, self-adjointness, spectral identification, binding, ground-state uniqueness, or approximation theorem was found in the reviewed accepted statements. No computational or bit-complexity claim follows from these files.

## Accepted build and audit evidence

The declared compiler is the project's pinned Lean 4.34.0-rc2. New proof modules were compiled from their final sources, using the pre-existing pinned mathlib/dependency and prior-audit object cache. This review's expanded statement files import those newly compiled objects. They are not an isolated source rebuild of the entire dependency closure; the separate reproduction branch owns that evidence.

The three successful independent audit runs are:

- `formal_semantics/20260909T230504_527537Z/receipt.json`: 48 graph, weak-domain and permutation declarations.
- `formal_semantics/20260909T230504_380738Z/receipt.json`: 24 declarations in the classical Hardy chain.
- `formal_semantics/20260909T230700_643543Z/receipt.json`: 4 classical-to-weak domain declarations.

All 76 requested declaration types compiled and all 76 requested axiom-dependency outputs appeared. These counts include definitions and abbreviations, not only theorems. Every source and object hash was unchanged across its audit run. The source token scan found no `sorry`, `admit`, added `axiom`, or `native_decide`; recursive axiom lists contained only `propext`, `Classical.choice`, and `Quot.sound`, or no axioms. No additional trusted computation mechanism is counted as kernel verification.

The expanded output exposes mathematical implicit arguments, universes and definitions while suppressing the implementations of inferred typeclass instances and proof terms occurring inside types. These display settings do not suppress mathematical hypotheses. Exact source and object hashes, final audit receipt hashes, and independently checked declaration coverage are in `FORMAL_SEMANTIC_REVIEW_MANIFEST_v2.json`.

Collision nullity separately has a successful proof build and expanded audit: `../lean/logs/collision_nullity/build-receipt-20260909T225022Z.json` records the successful theorem-module build, and `../lean/logs/collision_nullity/expanded-receipt-20260909T225413Z.json` records the corrected expanded audit. The earlier expanded invocation in the first receipt failed on an obsolete pretty-printer option; it is not counted as accepted evidence.

This reviewer retained three unsuccessful audit attempts: one root-directory invocation error, one deliberately terminated redundant typeclass-expansion run, and one successful Lean invocation whose Python postprocessor failed to parse multiline universe-decorated axiom output. The clean final runs above supersede them as evidence. None is a mathematical source-proof failure. Earlier development proof failures remain in their original logs; their transient `sorryAx` outputs are not accepted theorem evidence.

## Provenance and remaining frontier

Historical context: `THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. No claim in that report is used as an axiom here.

The actual imported physical definition source is `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/lean/ContinuumFoundation_v1.lean`, SHA-256 `4404491d04595f9a4361b07371ebcb4d1e015c011000d0456d0455c67865698e`. The inspected prior closedness/completeness source is `THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/lean/FermionicClosed_v1.lean`, SHA-256 `46e458bc478f216ba82574a4d84fd692f58c13a275c9ef1fc21185ec4ee35f2e`. No frozen or completed prior artifact was altered by this review.

At this checkpoint F02 is still incomplete: complex and weak-Sobolev Hardy extension, configuration slicing, spin summation, quantitative Coulomb bounds and the infinitesimal Laplacian relative bound remain to be connected in Lean. Ordinary L² density of smooth compact functions would not by itself supply the function-plus-gradient approximation needed for the weak-H¹ extension. F03 and F04 remain incomplete: this audit does not establish dense definition of the full intended realization, symmetry, self-adjointness, semiboundedness, or equality of variational and spectral ground energies. Full Theorem T remains unverified. Later proofs require a new dated supplement to this completed review.
