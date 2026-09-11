> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# PowerSeriesLocalDerivativeBound_v1 exact checkpoint

An actual HasFPowerSeriesOnBall f p x R, positive s : NNReal, and r+s<R give C>0 before every translation z with ||z||₊≤r and every order k, such that ||iteratedFDeriv ℝ k f (x+z)||≤k!*(C/s^k). For AnalyticAt ℝ f x, obtains rho,C,A>0 before all y in ball(x,rho) and all k, with actual derivative operator norm≤C*A^k*k!. Domain and complete target are normed real spaces.

The proof uses PowerSeriesUniformTranslationBound_v1, source SHA-256 `3fea11d14c340071a487c54854aee1242f6f5f9f98dbe5e81c2c65124c5441af`, and the sealed actual center permutation/operator-norm estimate. A single summable coefficient majorant is selected before the translated point and order.

Compiler PASS on first attempt using check_module_v2.py and pinned objects; no dependency rebuild. Approved v6 strict audit PASS: audits/formal_semantics/20260910T215613_260373Z/receipt.json. Both expanded statements and their complete axiom reports read. Only propext, Classical.choice, Quot.sound; no forbidden source tokens, printer ellipses, failures, fallback or omissions. Source and object unchanged during audit.

Source SHA-256: `73b4f7f62b97130b2b1e3b8a7a99bf2c46b3928987db936da0f21dbff76625a9`.
Object SHA-256: `d024b0ace79969f818b019dd66111f7014e6c14969a7cfd1a767f125908283bb`.

This proves actual local all-order growth from analyticity. The compact finite-subcover wrapper and physical coefficient analyticity are separate modules. It does not promote fixed-order smooth compactness to all-order growth. Constants are existential, not computable; original T02 remains unverified. Older PASS sources, frozen artifacts, historical audit records and shared ledgers remain unchanged.

Historical context: frozen relative path `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, frozen commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`, recorded in `THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`.
