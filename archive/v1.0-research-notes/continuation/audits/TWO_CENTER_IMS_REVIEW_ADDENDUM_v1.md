> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Final-source reconciliation for the IMS review

The completed `TWO_CENTER_IMS_ROOT_REVIEW_v1.md` remains unchanged. Its reviewed program is still SHA-256 `a0897a209a623290c6fcc088ecdc1b4a9bed98c27efd1e4840bf85f0c9507d01`.

The final paper `../computation/box/TWO_CENTER_IMS_v1.md` is now SHA-256 `355910471e5c2671bc3ce49d13c9f7f102e8ef6da87760f407fa3a131866ac2c`. The added general linear-partition corollary is valid. For z_max=max(z_L,z_R), the two nonnegative opposite-center weights have sum at most 1/d before charges are inserted, and the hydrogen contribution is at most z_max²/2. The interior IMS cost is exactly π²/(32d²); each exterior half-space cost is below the same bound. Thus E_el>=-z_max²/2-z_max/d-π²/(32d²).

The explicitly normalized stronger-center hydrogen exponential is an admissible H1 trial for the actual two-center form. Its additional Coulomb attraction is integrable and nonpositive, so E_el<=-z_max²/2. This yields the stated quantitative separation limit and permits addition of the independent clamped-nucleus repulsion constant. It asserts no excited-state separator or binding conclusion. The hydrogen trial and molecular spectral/form realization are paper dependencies here, not newly Lean-verified implementation facts.

No error was found in the added corollary. The remainder of the previously reviewed proof and exact program retains the prior review scope; actual timing and replay claims are supported by their separate execution records. This new addendum preserves the completed older review and molecular seal.
