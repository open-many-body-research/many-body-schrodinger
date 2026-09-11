> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual inner weighted norms from a weak Grushin cutoff

This unit establishes the local norm comparison consumed by R18. It is a formal mathematical theorem, conditional on genuine weak derivative and PDE inputs; it is not a certified computation or a factorial recurrence.

Let the domain be the actual product space R^4 x R^3 with product Lebesgue measure. Let U and H be complex L2 functions, with genuine global first and ordered second weak derivative witnesses d and e. Assume U has support, up to a null set, in a compact K and satisfies P_c U=H against all real smooth compact test functions, where P_c=-Delta_y-c|y|^2 Delta_t and c>0. Suppose K lies in one coordinate slab |y_i|<=R, R>0, and |y|<=S on K, with S>=1.

Fix a natural-index family F and a base index (a,b). Assume its shifted fields F(a+alpha,b+beta) have genuine local weak Y and T chains through order two on a region Omega. Let V be open with V contained in Omega. If U=eta F(a,b) almost everywhere and eta=1 on V, then every weighted field in the original outer index set is L2 on V and

    factorialLocalOuterNorm F V a b
      <= 498*S^2*(4*R^2+2*R+2+2/c)*||H||_2.

The outer index set and local norm are the existing exact definitions. The number 498 is the proved cardinality of that set, not an approximation size. No additional base-index cardinality is introduced here.

The proof has three parts. First, actual weak word-family uniqueness identifies the canonical first and second jets of U with the shifted natural fields on V. This includes zeroth order and needs only local almost-everywhere equality there. Second, each global weighted L2 representative restricts to the corresponding local field with norm at most its global norm. Weighted MemLp is proved before taking real values of extended L2 norms. Third, the existing compact weak Grushin maximal theorem supplies the explicit bound for the canonical global representatives. The comparison itself has factor one.

The cutoff function need not be smooth in this comparison theorem because its actual global H2 product and plateau equality are already premises. Smooth cutoff construction and the actual product PDE are separate previously developed inputs. The result does not manufacture these premises from a formal symbol. It does not claim unweighted second T control at y=0, smoothness of F, or estimates of arbitrary derivative order.

New source modules:

- WeakFactorialLocalFamilyMatch_v1: local natural/word weak derivative identification.
- WeakFactorialLocalOuterBound_v1: local weighted norm bounded by actual global representatives.
- WeakFactorialPlateauOuterBound_v1: shifted plateau comparison and actual-output bound.

All four new declarations compiled in pinned Lean 4.34.0-rc2 and passed the approved v7 expanded-statement and axiom audit at audits/formal_semantics/20260911T001802_240890Z/receipt.json. Only propext, Classical.choice and Quot.sound occur. Prior pinned dependency objects were reused; this is not an isolated source rebuild. The one failed wrapper elaboration is preserved: it required unfolding two existing definitions in the final comparison, with no change of statement or mathematics.

The next application composes this comparison with the actual mixed cutoff equation, its source/profile output bound, and the finite maximum defining the profile. Those are separate obligations and are not asserted discharged by this unit alone.

Frozen provenance: RWA_REPORT.md, SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066; frozen commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660; tag theorem-t-proof-freeze-2026-09-09; snapshot THEOREM_T_FREEZE_2026-09-09_212604/. No frozen artifact was changed.
