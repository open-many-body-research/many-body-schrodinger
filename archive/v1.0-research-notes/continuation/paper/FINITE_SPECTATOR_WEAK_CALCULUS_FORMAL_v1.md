> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Finite tangential weak PDE calculus

On the actual product space R4 x Rm with product Lebesgue measure, let Omega be open, B a real smooth coefficient on Omega, c any real number, and M a finite derivative order. Suppose raw families G_w and F_w are locally L2 for all ordered spectator words of length at most M, with genuine compact-test identities D_j G_w=G_(j::w) and D_j F_w=F_(j::w) below order M. Assume only the empty-word equation (P_c+B)G_empty=F_empty, where P_c=-Delta_y-c|y|²Delta_t.

Then every supplied word satisfies the genuine weak equation

(P_c+B)G_w = F_w - sum_proper_splits(a,b) (D_a B)G_b.

Each split preserves the original direction order in its coefficient and solution subwords. Repeated choices are retained in a list, giving exactly 2^|w| terms before removing the single all-solution term. Every proper split has positive coefficient order, strictly smaller solution order, and |a|+|b|=|w|. The RHS is proved locally L2, and both sides of every tested equation are integrable.

The proof establishes the raw local weak product rule, its finite-sum algebra, and the ordered Leibniz formula. It then differentiates the principal equation by the previously verified actual spectator commutation and restores B. No derivative-order commutation, smoothness of the solution, or higher-word PDE is assumed. The initial derivative families are substantive hypotheses; the theorem does not itself construct them. This is the conditional calculus step used before a genuine k-to-k+1 gain on smaller domains.

Six compiled modules and 29 exact declarations have a complete strict expanded-statement/axiom audit, with only propext, Classical.choice and Quot.sound (and empty dependencies for two pure definitions). The source-hashed adversarial note records the precise attempted failures and limitations. The v3 audit compiled successfully but its parser did not recognize Lean's explicit empty-axiom report. Preserved v4 adds only that exact report form; root independently reviewed this parser correction. No mathematical statement or proof was changed to repair the report.

This unit does not establish H12, numerical derivative bounds, factorial growth, analyticity, a smooth representative, or Theorem T. Its next use is finite derivative-family extension by the existing one-step weak gain. Pinned Lean 4.34.0-rc2 dependency objects were reused; these new modules were not included in an isolated source rebuild. Rungs 3-6 and unrelated regularity remain deferred under the sealed OPEN review. No novelty is claimed.

Sources, objects, review, parser review and audit receipt are bound by audits/FINITE_SPECTATOR_WEAK_CALCULUS_CHECKPOINT_v1.json. Preserved original RWA_REPORT.md SHA256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09, snapshot THEOREM_T_FREEZE_2026-09-09_212604/.
