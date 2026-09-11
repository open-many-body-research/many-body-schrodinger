> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual finite spectator iteration: adversarial review v1

Date: 2026-09-10. Reviewer: `/root/local_elliptic_gain/product_local_h2`.

**Finding:** no mathematical or semantic defect was found in the four new iteration modules. The endpoint constructs genuine finite spectator derivative families from an initial raw function with a region L² budget. It does not assume input solution derivatives. It retains the stated Y/YY reserve and propagates the displayed explicit budget.

This was a bounded read-only review. No compilation or Lean source changes were performed. The coordinating agent reported first-compile PASS and a pending strict v5 audit. This note records semantic review separately from those receipts. The reviewer authored the two arithmetic budget dependencies, so review of those dependencies is not independent. Their completed strict receipts are `formal_semantics/20260910T204614_195134Z/receipt.json` and `formal_semantics/20260910T204826_802416Z/receipt.json`. Reported builds reused pinned dependency objects.

## Exact sources

Paths are relative to `../lean/` from this note.

| Source | SHA-256 |
| --- | --- |
| `SpectatorIterationState_v1.lean` | `79442716cfa5067a3a6b4306f334ceca0f60c99c914dd915a82397b05412206d` |
| `SpectatorIterationStep_v1.lean` | `5903b567b9ed88d96ca1c1c8e2559fb6f31f2fe29b3ca9d92471d31d13cc5703` |
| `SpectatorIterationGeometry_v1.lean` | `b6754bd6c3cdb9082f00d9cad4d20280de2403eafa3edd753ce2c047afc17a68` |
| `SpectatorFiniteIteration_v1.lean` | `a469c41d89c5df3c1340d4bd446d8677a50e4fe98c132e83d62b754aab6f240d` |
| `SpectatorFiniteFamilyExtension_v1.lean` | `2ee5c978a92ee1748121a588aca8435d9b35c696af87ba4f4881fb88d158f025` |
| `SpectatorIterationBudget_v1.lean` | `ef98de887a1dfc3d1a1e481bfc2a7fc505ec40004dfa6c5aefd9b17a9a10c145` |
| `SpectatorIterationBudgetSequence_v1.lean` | `6762901e33dba1e939d28437147d665fad24de4184aad57b77c436b8e46b59c4` |

The four new modules and the exact family-extension implementation were inspected. The previously reviewed reserve/gain interfaces and the actual global-to-restricted L² inequality were checked only as needed for this composition. No broad dependency audit was repeated.

## Endpoint and derivative order

`spectatorFiniteState_iterate` assumes an initial `RegionL2Budget f (Ω 0) Winit`, namely actual `MemLp` for restricted volume together with its integral bound. It assumes the original compact-test PDE for f, a smooth potential, and forcing derivative data. No solution derivative, `SpectatorFiniteState` of positive order, Y derivative, or H² premise is an input to the final theorem.

For n stages, the forcing functions and potential coefficient budgets are required only for words of length `<n`, hence through order n−1 when n≥1. The forcing-chain condition `|w|+1<n` identifies each supplied next forcing derivative within that range. At stage i<n, the existing finite equation needs forcing and coefficient words through order i, and forcing derivative links with |w|<i. These are exactly available. No derivative of order n is silently required of the forcing or coefficient budget. Potential smoothness on the initial region remains an explicit separate hypothesis.

At n=0 the conclusion is the initial L² state and has no derivative content. Its forcing assumptions are vacuous, and the displayed PDE is unused. For n≥1 the empty-word forcing has the required L² membership, so the relevant tested PDE integrals are justified by the existing local integrability machinery.

## The actual i-to-i+1 step

The step unpacks the existing state only through order i. For each word w of length i, the finite equation is derived from the original PDE and the existing chain. The genuine one-step gain then constructs new global L² Y-first, T-first, and ordered YY witnesses for the cutoff of G_w. No new derivative or new derivative estimate is supplied as a hypothesis.

`spectatorFamilyExtend` leaves every word of length ≤i unchanged pointwise, including the empty word f. At a new word j::w with |w|=i it uses the constructed T witness for G_w. The local test identity for that witness supplies the new derivative link. The exact family-extension theorem checks both the older and the newly introduced links. The convention remains `j::w = D_j(D_w)`.

For the Y/YY reserve, words of length <i keep the original global L² witnesses unchanged; words of length i receive the new witnesses. The old local identities restrict to the smaller domain. The global weak derivative relation `D_yj gy_i=hyy_ij` is preserved without modification. Consequently hyy supplies the local ordered `D_yj D_yi G_w` identity on the final region by applying the first identity to a differentiated test. Those tests retain their support. There is no assertion that the raw G_w has these derivatives globally.

## Domain and norm checks

`SpectatorStepGeometry` contains concrete open-region, smooth compact-cutoff, plateau, and pointwise cutoff bounds. It contains no derivative-existence conclusion or gain estimate. Its domain inclusion is proved: χ=1 on the next region puts that region in `tsupport χ`; η=1 on the intermediate region then puts it in `tsupport η⊆Ω`. Induction yields `Ω i⊆Ω 0` for i≤n. Smoothness, forcing data, coefficient bounds, and the original test PDE are restricted along these actual inclusions.

The terminal Ω n is a supplied plateau region; the theorem does not assert it is open or nonempty. Its exact conclusion concerns tests supported there. Applications requiring an open nonempty target must supply such a cutoff chain. Existence of that chain is not proved by this four-module composition.

`RegionL2Budget` uses restricted-volume norms for the raw G words. Restriction lowers their nonnegative squared integrals. New T witnesses have a global summed squared norm bound; each component is bounded by that sum, and its integral on the next region is bounded by its global L² norm. These are the justified transitions used to extend the state. Earlier Y/YY witnesses retain their global norm bounds, which are then enlarged only by `W_i≤W_(i+1)`.

The recurrence is applied only at i<n. No positivity or geometric hypotheses on unused later cutoff-array entries are needed. Its next budget covers the inherited budget and each produced Y/T/YY bound. The proof's chosen constants are the displayed formulas, not an unspecified sequence of estimates.

## Exact strength and remaining work

At stage n, the state contains G_w through |w|≤n, with genuine local spectator derivative links. For every |w|<n it retains first Y and ordered YY witnesses. Thus n=12 includes spectator words through order 12 and the Y/YY reserve through spectator order 11, including first Y derivatives at order 11.

The common budget bounds each word's G integral and each word's Y/YY component sum. It does **not** bound a sum over all spectator words by that same number. Any later aggregate Sobolev estimate must account for that finite indexing and any required mixed-derivative identities. This endpoint does not alone identify a complete isotropic H12 norm or provide factorial growth, analyticity, or a radius-uniform bound. Initial data must satisfy a finite region L² budget, and the coefficient budget is on the entire initial region; mere local L² without these budgets is a weaker input class.

Witness selection is mathematical existence using the declared classical foundation. The explicit norm recursion is not an executable solver, and no bit-complexity or full Theorem T claim follows from this result.
