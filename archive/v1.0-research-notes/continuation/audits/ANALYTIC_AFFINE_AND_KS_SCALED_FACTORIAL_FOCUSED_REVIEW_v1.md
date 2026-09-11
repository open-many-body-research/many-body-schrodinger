> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Focused exact-source review: analytic affine and physical scaled factorial bounds

Reviewer: /root/finite_affine_jets. This is an independent read-only source and hypothesis review, not a replacement for the compiler, exact-statement printer or axiom audit. The root owns those checks. No Lean source, dependency object, historical audit or shared ledger was modified; no compiler or auditor was run by this reviewer.

Reviewed exact PASS source bytes:

- lean/AnalyticAffineCompactFactorialJets_v1.lean, SHA-256 `6dedf1afa3c8f6c043897171768190a423f91d3692ec489510c35a39121d35ba`.
- lean/KSScaledFactorialCoefficientBounds_v1.lean, SHA-256 `1a180a861d2315b5918ea50c6a1c71ce8b2a819b7a31a588af590c2b35d450de`.

Conclusion: no source-level hypothesis, quantifier, factorial-order, scaling or source-sign defect found within the stated scope.

## Quantifiers and true all-order input

The generic result assumes genuine AnalyticOnNhd for both fixed real functions on a compact K. It obtains C0,A0 and C1,A1 from analyticOnNhd_compact_factorial_bound before introducing eps, derivative order k, point x or constant source amplitude a0. It chooses C=C0+C1 and A=A0+A1 once; both are at least one. The estimates then hold for every eps in [0,1], every natural k, every point of K and every complex a0.

The proof's bound is the norm of actual iteratedFDeriv, with the factor (k.factorial : real) at every order. It does not use an order-by-order compact maximum or a finite reserve m. Although the source imports the earlier finite smooth affine module, the all-order bound is obtained from the analytic compact theorem. The reviewed analytic compact source applies one local all-order estimate at each compact-set point and one finite neighborhood subcover; the local source uses a uniform translated power-series coefficient estimate followed by the actual derivative/permutation norm bound. Thus the source-level argument does not promote mere C-infinity smoothness to analyticity or factorial growth.

## Affine estimates and the small parameter

The unscaled family is exactly f0+eps*f1. For eps in [0,1], the triangle bound uses norm(eps)<=1 and monotonicity of the nonnegative bases A0,A1. The scaled family is exactly eps*(f0+eps*f1). Its derivative is obtained by constant scalar multiplication, retaining an explicit eps on the right: eps*(C*A^k*k!). In particular eps=0 is included, with zero scaled coefficient, and no division by eps occurs. The complex source uses actual constant-vector scalar multiplication; its bound is (C*A^k*k!)*norm(a0), with constants independent of a0.

## Actual physical coefficients

The physical theorem instantiates f0 with nuclearKSPotential i Z 0 or pairKSPotential Z 0, and f1 with -8*E*norm(y)^2 or -4*E*norm(y)^2 respectively. These are the exact existing energy-affine identities, not a replacement coefficient. The energy polynomial is proved ContDiff at omega and then AnalyticAt, rather than inferring analyticity from ContDiff infinity. The zero-energy coefficients use actual nuclear or pair AnalyticAt on the genuine coefficient patch.

The first physical bound concerns the full nuclearKSPotential i Z (eps*E) or pairKSPotential Z (eps*E). The second concerns the existing epsilonNuclearKSPotential or epsilonPairKSPotential definition, exactly eps times that full coefficient. This retains eps times all interactions and eps squared times physical energy, including the repulsive pair constant. The third concerns the exact normalized forcing p -> potential-at-scaled-energy p smul (-a0). Its minus sign is retained by specializing the generic source theorem to -a0, and norm_neg gives norm(a0). It introduces no inverse eps and does not bound a different sign or amplitude function.

## Scope and limitations

Constants precede eps, k, point and a0. They may depend on the fixed compact K, fixed Z,E and, for the nuclear theorem, fixed N and selected i. These theorems do not alone assert one pair of constants simultaneously for varying N,i,Z,E,K or a varying chart center. A later common compact-region instantiation can address uniform chart centers. Compact inclusion in the actual nuclear/pair patch is an explicit premise, and no y-nonzero premise is added: the relevant regularized collision fiber remains covered wherever the true coefficient patch allows it.

The results are coefficient derivative estimates only. They assert neither weak-solution regularity, H12, an all-order PDE induction, computable numerical constants, nor original T02 verification. Root-managed strict auditing of these modules and the translated-series dependency remains separate from this source-level review; no transitive scanner success is inferred here.

Historical context: frozen relative path `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`, inventory `THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`. All historical and PASS bytes remain preserved.
