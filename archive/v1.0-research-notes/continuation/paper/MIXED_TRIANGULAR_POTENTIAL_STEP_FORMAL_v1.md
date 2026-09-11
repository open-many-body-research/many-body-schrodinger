> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Quantitative triangular Y recovery from the actual potential equation

The exact formal step starts from (P_c+B)f=s on an open product region, where P_c=−Δ_Y−c|y|²Δ_T and B is real and C∞ on the region. An existing genuine mixed weak derivative reserve through Y order r and total order m is the input. Two supplied compact smooth cutoffs define the next region. The step constructs a reserve through Y order r+2, still at total order m. It assumes no new Y derivative or positive-order PDE.

Every right side is derived from the original equation. For canonical ordered words a,b, the identity is

    −Δ_Y F(a,b) = S(a,b) − D_Y^a D_T^b(Bf)
                   + c D_Y^a(|y|² Σ_j F([],j::j::b)).

The potential product is an exact double ordered Leibniz sum with repeated choices retained. Its weak derivative identity follows from local smooth-coefficient Leibniz. Finite spectator differentiation supplies the initial equation; two actual weak spectator integrations move the weight c|y|²; finite Y differentiation then supplies the displayed equations. All test integrals are proved integrable. The quadratic term has a plus sign.

Write d=card κ, and let W bound the squared L2 norm of every existing solution jet, H0 the corresponding source-jet budget, K0 a bound for the actual mixed coefficient derivatives, and Q0 a bound for actual Y derivatives of |y|². Only source/coefficient derivative bounds with total order at most m−2 are used in this Y stage. The regularity hypothesis on B remains C∞; this is not a finite-C^(m−2) theorem. A common forcing budget is

    R = 3 H0 + 3·(2^m)^2 K0² W
              + 3 c²·(2^m)^2 d² Q0² W.

For cutoff constants M,A,L,D,Q satisfying the explicit geometric hypotheses, set

    C0 = 4 A² + 16 L(D/2+Q),
    C1 = 2 M² + 8 L D,
    Wnext = max(W, (3/2)(C0 W + C1 R)).

The theorem constructs every new weak jet with squared L2 norm at most Wnext on the smaller region. The word-count and dimension factors are explicit. The proof uses second-Y gains at precursor Y lengths r−1 and r, each total order at most m−2; local weak uniqueness attaches their representatives to the old family and to one another. This handles the odd boundary without requesting total order m+1. The new representatives are selected noncomputably for this analytic existence theorem; no executable procedure or complexity guarantee is asserted.

Evidence: the six principal source modules compile and pass v5 expanded-statement/axiom audits, fifteen declarations total. Only propext, Classical.choice, and Quot.sound occur. Exact final statements and relevant packaged definitions were read; all PASS bytes remain unchanged. Failed proof-tactic attempts in the final arithmetic conversion are retained. The empty/m<2 formal cases add no unavailable jets, and the concrete target uses m=12.

The initial r=2,m=12 state comes from the separate actual finite spectator iteration. Repeating the present step five times gives the intended triangular reserve; its iteration and coordinate/multiindex extraction are separate compositions. This checkpoint alone is not a complete H12 initialization. Its constants are a verified variant and do not preserve the frozen H8/H4 constants automatically. No factorial analytic estimate, global dictionary approximation, certified energy algorithm, or full Theorem T follows from this checkpoint alone.

Reproducibility scope: pinned library and prior continuation object caches were reused. These modules lie outside the earlier 671-target isolated source-rebuild snapshot; no new rebuild was attempted under the current priority restriction. Frozen provenance: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09; frozen report THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066. Frozen artifacts, previous successful sources, and prior logs remain unchanged.
