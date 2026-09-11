> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Fixed compact two-electron KS chart checkpoint

Created 2026-09-10. This is a new R01/Rung 2 initialization prerequisite.
Original T02 remains unverified.

Historical context: frozen `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, from
`THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`; frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. No frozen or prior PASS artifact was edited.

## Exact region and conclusions

`lean/KSFixedChartPatch_v1.lean` defines `ksFixedChartRegion t0` in the existing
`PairKSSpace` as the product of the closed KS ball centered at zero with radius
`1/4` and the closed spectator ball centered at `t0` with radius `1/4`.
Here `t0 : SpectatorConfiguration (0 : Fin 2)` and the patch results assume
`‖t0‖ = 1`. `PairKSSpace` is already defined as
`NuclearKSSpace (0 : Fin 2)`; no different spectator spaces are identified.

The module proves:

- Compactness and membership of `(0,t0)`.
- `3/4 ≤ ‖t‖ ≤ 5/4` and `‖ksMap y‖ ≤ 1/16` throughout the region.
- Both nuclear distances under the exact pair lift are at least `23/32`.
- Under the exact nuclear lift with selected electron zero, the other nuclear
  distance is at least `3/4` and the pair distance is at least `11/16`.
- Inclusion in both existing coefficient patches.
- Both exact physical lift norms are strictly below `2`.
- The pair lift has coincident positions at every `(0,t)`. Thus the selected
  pair collision fiber is included, including the center point.

The proof uses the existing norm-preserving `pairCenterEquiv` and exact lift
identities. There is no rescaling or Hamiltonian change.

## Verification

First compilation PASS:
`logs/development/KSFixedChartPatch_v1-20260910T205510_954514Z.json`.

Strict v5 statement and axiom audit PASS:
`audits/formal_semantics/20260910T205524_588060Z/receipt.json`.
All 14 local declarations were discovered and audited. The complete expanded
types were reviewed. There were no ellipses or forbidden source tokens; source
and object remained unchanged. Every declaration uses only `propext`,
`Classical.choice`, and `Quot.sound`.

- Source SHA-256: `b36d892dc6fe51e964982b90a8f4a95502e7bef83742e479e05a7e2d98e5764a`.
- Object SHA-256: `c5ff1f815ef5e4cff52ac1597a409131bf7b30ebd2ffd510d4523660e356e47d`.
- Expanded audit source SHA-256: `1a9f4225137ee1e6533c40c4bb6756751ca15d8603d51abd3a2b27dea8eb08b7`.
- Expanded audit log SHA-256: `a224d94fec6b9519bc00b12ae515784011058d79ecead30d5999cb7beea55b92`.

This reused the pinned dependency object cache, without a dependency source
rebuild. Seven-coordinate box inclusion, actual coefficient-bound
instantiation, amplitude bounds, and PDE estimates are separate work. This
checkpoint makes no H12 or T02 closure claim.
