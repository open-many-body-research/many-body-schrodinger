> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Raw local Grushin to Y-Laplacian extraction

Created 2026-09-10. New local equation prerequisite for the finite Y-recovery
schedule. Original T02 remains unverified.

Historical context: frozen `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256
`1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, from
`THEOREM_T_FREEZE_2026-09-09_212604/FREEZE_MANIFEST.json`; frozen commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. No frozen or prior PASS artifact was edited.

## Exact scope

`lean/LocalWeakGrushinYEquation_v1.lean` contains four declarations in
`TheoremT.Continuum.WeakGrushin`:

- `local_spectator_invariant_weight_second_test` transports an arbitrary smooth
  Y-only real weight through two actual local weak spectator derivatives. It
  proves both compact-test integrands are integrable and gives the exact
  second-derivative testing identity.
- `local_grushin_y_source_locallyL2` proves the raw local L2 membership of
  `h + (c*‖y‖^2) • sum e` from local L2 membership of `h` and every `e`.
- `grushin_y_test_identity` proves the operator identity
  `P0(phi) = Pc(phi) + c*‖y‖^2*sum Dtt(phi)`.
- `local_grushin_to_y_equation` combines the identity with two weak integrations
  by parts in each spectator direction, producing the actual compact-test
  equation `P0 f = h + (c*‖y‖^2) • sum e`, with a **plus** sign.

The main theorem assumes raw local L2 membership of `f` and `h`, the actual
compact-test equation `Pc f = h`, and actual `ProductLocalWeakDirectional`
relations from `f` to `d j` and from `d j` to `e j` in `tDir j`. That relation
includes local L2 membership of both functions. The conclusion supplies local
L2 membership of the new source and integrability of both Y-equation test
integrands. No global Lp representative, global derivative, or H2 hypothesis
appears. No openness assumption or restriction on the real scalar `c` is needed
for this extraction identity.

The domain is the existing `Space kappa`, with four Y coordinates and the
existing finite spectator coordinate type. The measures are its existing
product Lebesgue measures. Potential terms, when present, must first be moved
to `h` by a separate actual weak-equation reduction.

## Verification

Compilation PASS:
`logs/development/LocalWeakGrushinYEquation_v1-20260910T211616_505890Z.json`.
The compiler reports only a nonfatal unused `DecidableEq` section variable in
the source-local-L2 helper.

Strict v5 expanded-statement and axiom audit PASS:
`audits/formal_semantics/20260910T211634_598750Z/receipt.json`.
All four declarations were discovered and audited; complete expanded types
were reviewed. No forbidden token, ellipsis, or unexpected axiom was present;
source and object remained unchanged. Only `propext`, `Classical.choice`, and
`Quot.sound` occur in the kernel axiom reports.

- Source SHA-256: `202151aa6f3b1274b646c656f7d832f3194cb5e6b395efe9c4023cd285904ba8`.
- Object SHA-256: `be50779594002cef88cdb789de86884091ca642eff8612b9974147db20bfb9cf`.
- Expanded audit source SHA-256: `13b012bc0bae4d7b598b1e7e3d88af8643a33f7a6583005cc155dfc31e88523b`.
- Expanded audit log SHA-256: `35fc77f27b470e43e425bd6a6b118fc0c808c0c42259b0dced78fc24e970f2ae`.

Pinned dependency objects were reused; no dependency source rebuild was run.
This is an equation extraction theorem. It constructs no new spectator jets,
gives no derivative norm estimate, and does not establish H2, H12, a finite
recovery schedule, or original T02.
