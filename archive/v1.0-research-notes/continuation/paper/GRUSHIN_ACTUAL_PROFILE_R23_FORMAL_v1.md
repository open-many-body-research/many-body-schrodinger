> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# R23 for the actual weak derivative profile

Fix the actual product space R^4 x R^3, product Lebesgue measure, and P_c=-Delta_y-c|y|^2 Delta_t with c>0. Let the outer rectangular box have center a with a_y=0 and half widths aY,aT. Assume 0<rho<=1 and rho<aY,aT.

The theorem uses one natural weak derivative family F throughout all orders and shrinking boxes. Its inputs are the original weak equation (P_c+potential)F(0,0)=src, genuine local Y/T weak chains, finite L2 budgets at each finite order (with no prescribed order dependence), and one actual finite H12 budget W. The H12 family may be separately selected: local weak uniqueness transfers its budget to F. The potential and source are smooth on the outer box and satisfy actual factorial bounds on ordered coordinate derivatives, with constants M,A,F0, A>=1. These bounds concern the coefficients and source; they are not estimates on the unknown solution.

Define

    S = max(1,2*aY),
    H0 = 498*S^2*sqrt(W),
    C = factorialProfileRecurrenceConstant(c,aY,rho,C1,C2,M),
    B = 2*C*A.

Here C is the existing fully specified localized coefficient, including the actual graph and cutoff constants. C>=1 follows from its defining maximum. C1 and C2 bound the first and second derivatives of the actual Real.smoothTransition cutoff. For every natural r, the literal profile satisfies

    factorialBoxProfile F a aY aT r rho
      <= 2*B*(F0+H0)*(2*B*(r+1)/rho)^r.

The profile is the finite maximum of sums of actual restricted weighted L2 norms, using the exact 498-term outer index set. The proof supplies all weighted MemLp needed for those real-valued norms. A second theorem constructs actual L2 representatives for every shifted outer field of base cost at most r, with norm equal to its local outer norm and bounded by the same displayed quantity.

No recurrence, monotonicity, base profile estimate, or solution factorial estimate is assumed. The actual PDE yields the recurrence through GrushinActualProfileRecurrence_v1. Genuine finite local budgets yield domain monotonicity of the profile. The centered box has Euclidean Y radius at most 2*aY; the actual finite H12 theorem and cross-family weak uniqueness give the base bound uniformly for r<=8 on every nonnegative box shrink. The previously verified scalar fixed-gap argument then gives the displayed estimate without dividing by F0+H0, so zero amplitude is included.

This unit retains the existence of one genuine all-order weak family with finite local budgets as an explicit premise. Removing that premise from a raw locally L2 PDE input is a separate formal wrapper. It also retains actual coefficient/source bounds and the supplied H12 budget. The result does not yet claim pointwise derivative bounds, an analytic solution representative, or efficient computation.

New integration source: GrushinActualProfileBound_v1. The centered base geometry helper is FactorialCenteredBoxBaseProfile_v1. Sources and objects are preserved after their successful builds. Compilation uses pinned Lean 4.34.0-rc2 with cached dependency objects; it is not an isolated source rebuild. Exact compiler, approved v7 expanded-statement/axiom evidence, and independent review are linked in the accompanying checkpoint.

Frozen provenance: RWA_REPORT.md, SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066; commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660; tag theorem-t-proof-freeze-2026-09-09; snapshot THEOREM_T_FREEZE_2026-09-09_212604/. No frozen artifact was changed.
