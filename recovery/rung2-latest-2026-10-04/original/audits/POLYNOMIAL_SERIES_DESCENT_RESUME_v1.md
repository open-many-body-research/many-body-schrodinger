# Polynomial-series descent continuation checkpoint

Owner: `/root/weak_pointwise_limit`. This new resume file records the state after the physical real mixed-derivative compilation and strict audit; it is not a completion claim for R04 or Theorem T.

## Verified checkpoints

- Actual separate-radius joint analyticity: `HOMOGENEOUS_SPECTATOR_JOINT_ANALYTIC_CHECKPOINT_v1.json`, SHA `1ba2900ba9e7c6a498031dfec33e24d3f91b2442cd0d18aab108b2b8ce47d65d`.
- Prescribed two-index real-input KS family, exact physical pair-index sum identity, derived absolute summability, D5 norm bounds and uniform convergence: `KS_REAL_SPECTATOR_SERIES_DESCENT_CHECKPOINT_v1.json`, SHA `6473920122c87249291ffaba58b9e653907856a2747edeefc027f9cea9e7a1a5`.
- Corrected mixed derivative bound with separate rates: `HOMOGENEOUS_SPECTATOR_MIXED_DERIVATIVE_CHECKPOINT_v1.json`, SHA `584ae07faf6d3b8838fb908e4a4731065d3b4d37bfb2172a1a774613c2f91aec`. Twelve primary declarations, compiler and strict PASS, full statements and axioms read, focused independent review passed.
- Exact real derivative restriction helper: `REAL_RESTRICTION_DERIVATIVE_WORD_CHECKPOINT_v1.json`, SHA `0f1b99e3b332c37e7fb384a00ded255c543f4adbb7f724a46f3c493fa54f1887`.
- Generic literal real mixed derivative bound: `HOMOGENEOUS_SPECTATOR_REAL_DERIVATIVE_CHECKPOINT_v1.json`, SHA `0b6be63deb9064d87e9c7fd69c18fcd1c5e3a1b09b04f322102882571ca2c867`.

## Current physical consumers

`PhysicalKSAnalyticDescentDerivative_v1.lean` source SHA `7b11fc65d94eadf122f68479dfd9ed8d9d160ec77a264038500deb21fd25a97f`, strict `20260911T030635_686458Z`, four declarations. Defines literal `physicalKSDescentDerivativeBudget` and proves nuclear/pair complex mixed derivative bounds from actual `PhysicalKSBoxPointwiseData`, actual finite physical Taylor coefficients and proved chart balance.

`PhysicalKSAnalyticDescentRealDerivative_v1.lean` source SHA `6abb68bcb4684c937d3f2f3599f830ec19379ee1cd1696486cedfd70e9d91121`, strict `20260911T030934_794599Z`, three declarations. Exact real restriction supplies the corresponding actual real-coordinate derivatives without changing constants. Both source bodies and all seven expanded statements/axiom reports have been read by the author. Focused independent physical review is finishing with `/root/weak_pointwise_limit/polynomial_norm_review`; bind its final JSON in the physical derivative checkpoint next.

Writing C=physicalKSPointwiseAmplitude(M,A,F0,W), S=7 physicalKSPointwiseRate(M,A), D=32 S^2, the A bound is 16 C (24 D)^|alpha| (24 S)^|beta| alpha! beta!, and the B bound is D times that quantity. Domains are D norm(X)_infinity <=1/4 and S norm(s)_infinity <=1/4. This is a corrected explicit constant on a smaller polydisc; the original sharper D6 claim remains separate.

## Active next actions

1. Read the final focused physical derivative review, verify all source/object/receipt hashes, and write `PHYSICAL_KS_ANALYTIC_DESCENT_DERIVATIVE_CHECKPOINT_v1.json`. Send path and hash to root.
2. Child `/root/weak_pointwise_limit/radial_coefficient_bound` is proving real-analytic fixed-spectator slices. It must include actual Position=EuclideanSpace(R,Fin3) and Euclidean spectator space, not silently replace physical norm by Pi sup norm. Exact domain D norm_Euclidean(X)<1 and S norm_Euclidean(T)<1, with the ball radius D^-1 for D>0. Root needs this for collision-centered norm-decomposition uniqueness.
3. Root owns actual physical sum identification/surjectivity and germ compatibility. Their compatibility theorem must use a common neighborhood containing X=0: A+norm(X)B is not a unique decomposition on arbitrary regions away from collision, because norm(X) is analytic there.
4. Continue the next concrete R04 obligation after these components. No repeated broad audit is needed.

No owned compiler or strict-auditor process remains live at this checkpoint. Child proof/review work remains active. There is no unfinished mathematical failing statement in the two physical derivative modules. Earlier compiler failures in the complex wrapper were function-unfolding/numeric-normalization bookkeeping; they were repaired before the immutable first PASS.

## Commands and trust

Use `/usr/bin/python3` with `login:false`. From the workspace root:

```
/usr/bin/python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/lean/check_module_v2.py MODULE
/usr/bin/python3 THEOREM_T_POST_FREEZE_WORK/CONTINUATION_2026-09-09_v2/audits/audit_final_statements_v8.py MODULES
```

One owned compiler/auditor at a time; wait for terminal status before the next. Preserve every first-PASS source, audit and checkpoint. Only propext, Classical.choice and Quot.sound are accepted foundational axioms here. Full statements must be read as well as axiom reports. Lean 4.34.0-rc2 and pinned Mathlib d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9 are used with pinned dependency/prior continuation caches; no new isolated source rebuild is claimed. Classical choices of finite words and multilinear representatives are mathematical definitions, not an executable certified energy algorithm.

Frozen reference: rwa_proof/THEOREM_T_COMPOSITION.md, SHA 1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. All frozen artifacts and prior successful continuation files remain untouched.
