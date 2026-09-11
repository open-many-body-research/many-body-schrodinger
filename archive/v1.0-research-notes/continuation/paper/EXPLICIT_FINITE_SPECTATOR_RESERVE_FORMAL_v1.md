> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Explicit finite tangential reserve

Let P_c=-Delta_y-c|y|²Delta_t on the actual product R4 x Rm, with c>0. Fix an open region Omega and smooth compact inner and middle cutoffs chi,eta, with eta equal to one on an open neighborhood of the support of chi and support eta contained in Omega. Fix displayed cutoff budgets M,A,B,D,Q exactly as in LocalWeakGrushinExplicitPotentialOneStep_v1: |chi|<=M, |combined scalar commutator coefficient|<=A, inner cutoff gradient weight<=B, eta²<=D, and middle weighted cutoff energy coefficient<=Q; B,D,Q>=0.

Before choosing any potential, derivative order, source or solution, the theorem chooses a compact K contained in Omega and an open V containing the middle support, with V contained in K. Let P be a real smooth potential on Omega, and let G_w,F_w be genuine raw local L2 spectator derivative families through a finite order m. Only the empty-word equation (P_c+P)G_empty=F_empty is assumed. Suppose, on this K, every actual ordered coefficient derivative D_a P with |a|<=m has absolute value at most K0, every integral of ||G_w||² with |w|<=m is at most W0, and every integral of ||F_w||² is at most H0. K0,W0>=0. These are coefficient and integral budgets, not pointwise solution estimates.

Set C0=4A²+16B(D/2+Q), C1=2M²+8BD. For a word w of length k<=m define the explicit scalar

J_k=(C0+2C1 K0²)W0 + 2C1[2H0+2(2^k-1)²K0²W0].

For every such word the theorem constructs actual global L2 witnesses gy_i, gt_j and hyy_ij. On any supplied plateau O where chi=1, gy_i and gt_j are genuine local weak Y and T derivatives of the original raw G_w. Every hyy_ij is the genuine global weak Y_j derivative of gy_i. Their bounds are

sum_i ||gy_i||² <= 2M²W0+3J_k/4,
sum_j ||gt_j||² <= J_k/(16c),
sum_i,j ||hyy_ij||² <= 3J_k/2.

The weak derivative identities identify these witnesses as derivatives of G_w on O; no smooth surrogate or new derivative hypothesis is substituted. In particular the Y-first witness at tangential order eleven is retained, so it is available for the total-order-twelve odd-Y endpoint. The result is an estimate for one finite stage, not yet the full twelve-stage H12 theorem.

The finite weak PDE calculus derives the exact proper commutator with 2^k-1 list terms. Every term uses a strictly lower solution derivative. Finite Cauchy and compact integral estimates give integral ||commutator_w||² <= (2^k-1)²K0²W0. The actual source R_w=F_w-commutator_w is locally L2 and has squared integral at most 2H0+2(2^k-1)²K0²W0. Applying the previously sealed explicit inhomogeneous one-step theorem and enlarging only nonnegative coefficients gives the displayed J_k. This composition introduces no unknown derivative norm of the next order on its right side and no existential numerical constant hidden in J_k.

The coefficient P is smooth in the current formal interface, though only the displayed finite derivative budgets enter this numerical estimate. The theorem does not supply those coefficient budgets, the initial source/solution budgets, or the twelve nested-domain induction. It does not recover all higher Y orders, establish H12, factorial estimates, analyticity or full Theorem T. Witness selection is an existence proof, not an executable derivative procedure; no novelty is claimed.

Four modules and six declarations are sealed with source/object hashes, final expanded statements, and axiom audits in audits/EXPLICIT_FINITE_SPECTATOR_RESERVE_CHECKPOINT_v1.json. Only standard foundational axioms are used. The original and explicit reserve modules were also read for their exact witness meanings and quantifier order. Pinned Lean 4.34.0-rc2 dependency caches were reused; these modules were not included in a new isolated source rebuild.

Frozen original RWA_REPORT.md SHA256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09, snapshot THEOREM_T_FREEZE_2026-09-09_212604/. All earlier PASS sources and preservation records remain unchanged.
