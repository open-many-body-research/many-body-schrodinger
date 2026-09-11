> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual compact weak H² localization energy

Evidence category: fully formalized mathematical results. Five new modules, fifteen declarations, two strict expanded-statement and axiom audits, standard propext/Classical.choice/Quot.sound only.

On actual R⁴×R^m product Lebesgue space, let f have compact a.e. support and genuine global weak H² witnesses d(v), e(v,w). For real smooth compact η, define the cutoff first derivative by A_v=η d(v)+(D_vη)f. Define E_c(ηf)=Σ_i∫|A_yi|²+cΣ_j∫|y|²|A_tj|² and C_c(η,f)=Σ_i∫|(D_yiη)f|²+cΣ_j∫|y|²|(D_tjη)f|². These are the actual product-rule weak derivative expressions; the product cutoff-jet module separately supplies their genuine weak derivative witnesses.

For every real c, the exact identity holds:

E_c(ηf)=∫Re〈η²f,P_c(e)〉+C_c(η,f).

Its proof constructs one-support smooth H² approximants. Generic bounded multiplication on the one compact support gives convergence of weighted two-field sums and real inner-product integrals, not merely scalar pointwise convergence. The already verified smooth identity passes to the limit.

For c≥0, with no supplied PDE output premise, the proved L² principal expression gives:

E_c(ηf)≤½(∫η²|f|²+∫η²|P_c(e)|²)+C_c(η,f).

When an actual L² h satisfies P_c f=h weakly only on an open Ω containing tsupport η, the same exact identity and Caccioppoli bound hold with h replacing P_c(e). No weak PDE premise outside Ω is required. This local-output version holds algebraically for every real c; a nonnegative left gradient energy requires c≥0, and later unweighted spectator coercivity requires c>0. The proof uses the separately verified local a.e. identification of the weak principal expression and makes no use of output values outside the cutoff support.

These statements concern inputs already known to have genuine weak H² jets. They do not assert joint H² from one weak Grushin equation. Preliminary partial regularization, uniform local estimates, and the μ→0 derivative-identification step remain separate tasks before the weak anisotropic gain is composed. No numerical algorithm, approximation rate, analyticity claim, or full Theorem T is asserted.

All five modules compile using the pinned Lean4.34.0-rc2 / Mathlib d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9 environment with existing compiled dependency caches. They are outside the sealed 671-target v18 source-rebuild snapshot. Frozen records are unchanged: commit166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09, frozen RWA_REPORT.md SHA-2562545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066.
