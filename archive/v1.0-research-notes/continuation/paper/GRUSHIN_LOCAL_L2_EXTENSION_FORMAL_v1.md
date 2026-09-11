> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Grushin local L² input extension, version 1

The local input gap identified in `audits/GRUSHIN_ONE_STEP_INTEGRATION_REVIEW_v1.md` is discharged. This is a fully formalized reduction from genuine locally square-integrable data to global L² representatives; it does not itself assert regularity gain.

Let T be any finite-dimensional real inner product space with its Borel structure, let b be an orthonormal basis indexed by a finite type, and take real c. The underlying space is the ordinary product R⁴ × T, with its maximum product norm and actual product Lebesgue measure. Write

P_c = −Δ_y − c |y|² Δ_t.

Suppose g and h are complex-valued functions whose restrictions to every compact subset of Ω belong to L², and suppose the actual compact smooth real-test equation ∫(P_c φ)g = ∫φh holds for every test supported in Ω. For every compact K contained in Ω, the formal construction produces the actual global L² classes G = 1_K g and H = 1_K h. Their chosen representatives equal the raw data almost everywhere on K and vanish almost everywhere off K. Moreover,

‖G‖₂² = ∫_K |g|², and ‖H‖₂² = ∫_K |h|².

The same weak equation holds for every compact smooth test supported in any U contained in K. When Ω is open and K₀ is any compact subset, a second theorem supplies compact K and open U with K₀ ⊆ U ⊆ K ⊆ Ω, together with these representatives and norm identities.

The proof uses the restriction/indicator equivalence for `MemLp` and `MemLp.toLp`. Test locality gives P_c φ = 0 outside the topological support of φ. Equality of the two integrands therefore follows from almost-everywhere equality on K; no derivative of the indicator is taken. Separate compiled theorems prove that the raw-data test integrands are integrable from the local L² hypotheses and smooth compact test support. Thus the PDE hypothesis cannot exploit the default value of a nonintegrable Bochner integral.

The result imposes no positivity on c because it proves locality, not coercivity. Empty compact targets and zero-dimensional spectators are included. It assumes no derivatives of g or h, no preliminary H² property, no binding or spectral hypothesis, and no global integrability of the raw inputs. All choices are mathematical existence constructions; this is not an executable numerical solver.

The main APIs are `grushin_local_l2_extension`, `grushin_local_l2_neighborhood`, `product_compact_intermediate_neighborhood`, and `grushin_local_l2_test_integrable` in `TheoremT.Continuum`. The compact-neighborhood helper can be applied directly to the support of a cutoff in the already compiled partial-regularization sequence.

Both new sources compiled with Lean 4.34.0-rc2 in the pinned environment. The strict expanded-statement and axiom audit at `audits/formal_semantics/20260910T174415_832468Z/receipt.json` jointly imports both modules and `GrushinPartialRegularizationSequence_v1`. All 12 audited declarations report only `propext`, `Classical.choice`, and `Quot.sound`; the report is complete, contains no printer ellipses, and preserves every source/object hash. Eleven declarations are new; the twelfth is the unchanged sequence theorem, imported to check compatibility. The proof sources and expanded final hypotheses were inspected for the actual operator, product measure, local support, L² exponent, and output quantifiers. No extra trust mechanism is used.

An independent subagent reviewed the exact new source hashes and relevant support/measure definitions, including empty-target and zero-dimensional edge cases, and found no defect. That review did not independently rerun compilation or the expanded audit. Agreement is supporting review evidence, not an additional proof.

Reproduction commands, run from the workspace root:

```text
/usr/bin/python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py GrushinLocalL2Extension_v1
/usr/bin/python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py GrushinLocalL2Neighborhood_v1
/usr/bin/python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/audit_final_statements_v3.py GrushinLocalL2Extension_v1 GrushinLocalL2Neighborhood_v1 GrushinPartialRegularizationSequence_v1
```

These checks reuse the disclosed pinned dependency object cache and newly compiled continuation objects. They are not an isolated source dependency rebuild. The new modules are outside the already sealed desktop rebuild capsule; that capsule's result cannot automatically certify them. No novelty claim is made for this standard localization argument.

Preservation: all work is in new continuation files. The frozen baseline remains commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`; its original `rwa_proof/RWA_THEOREM.md` has SHA-256 `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`. Frozen and previously successful source bytes were not changed.

Next composition: apply the global-L² local weak Grushin gain to the constructed representatives, then identify every cutoff output with the corresponding cutoff of the raw data. Uniform gain and full Theorem T remain separate obligations.
