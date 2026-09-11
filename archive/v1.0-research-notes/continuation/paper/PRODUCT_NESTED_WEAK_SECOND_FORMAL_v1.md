> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Nested cutoff weak second derivative

On the actual ordinary product of arbitrary finite-dimensional real inner-product spaces Y and T, let f,d,h,e be actual complex L² classes and v a product-space direction. Suppose the genuine compact-test weak derivatives satisfy Dᵥf=d and Dᵥh=e. Suppose h=θd almost everywhere and θ=1 on the topological support of a real C∞ compactly supported cutoff η.

The formal theorem constructs actual L² classes U,a,b with genuine weak equations DᵥU=a and Dᵥa=b, and proves

\[
U=\eta f,\qquad
 a=\eta d+(D_v\eta)f,\qquad
 b=\eta e+2(D_v\eta)d+(D_v^2\eta)f
\]

almost everywhere. It does not assume that d has a global weak derivative. It does not assume any continuity, differentiability, boundedness, or measurable representation of θ beyond the stated almost-everywhere relation and plateau values.

The proof applies the independently verified single-direction compact multiplier rule three times: to ηf, to ηh, and to (Dᵥη)f. The input of the last two resulting weak equations sums to the first derivative of ηf because ηh=ηd. Their outputs give the displayed second derivative because (Dᵥη)h=(Dᵥη)d. This second equality follows from the exact support inclusion support(Dᵥη)⊂support(η); it does not differentiate θ or any indicator. Addition and identification are operations on actual L² classes with genuine weak derivative proofs.

The theorem is `product_nested_weak_second` in `ProductNestedWeakSecond_v1`. Its two almost-everywhere plateau helpers are in `ProductNestedPlateauAE_v1`. The dependency modules `ProductCompactWeakDirectionalMultiplier_v1` and `ProductWeakL2Algebra_v1` are separately compiled and audited. Exact source/object hashes and strict expanded-statement/axiom receipts are recorded in `audits/PRODUCT_NESTED_WEAK_SECOND_CHECKPOINT_v1.json`. Only the declared standard axioms occur. Development reused pinned library and project objects; these sources postdate the completed v18 isolated source rebuild.

This is the calculus ingredient for composing an anisotropic derivative gain on an outer localization θd into actual same-coordinate second derivatives of ηf. The two-step Grushin regularity composition itself remains a separate obligation. No analytic rate, executable solver, numerical interval, novelty, or full Theorem T is claimed here.

Frozen artifacts remain unchanged: original `RWA_REPORT.md` SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`, freeze `THEOREM_T_FREEZE_2026-09-09_212604`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`.
