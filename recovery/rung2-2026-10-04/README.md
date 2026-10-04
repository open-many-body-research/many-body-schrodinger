# Rung 2 source recovery, 2026-10-04

This restores the original continuation sources and verification evidence requested by [issue #6](https://github.com/open-many-body-research/many-body-schrodinger/issues/6). It is a recovery package, with no evidence-tier promotion or change to the claims registry. Rung 2 and Theorem T remain open.

The [manifest](MANIFEST.json) binds the complete local import closure of the five requested proof roots to exact SHA-256 hashes: 1,159 modules, comprising 750 existing published foundation modules and 409 recovered continuation modules. The foundation is referenced at its existing paths and is not changed. Original flat module names and source bytes are retained in [sources/](sources/) so existing imports and declarations continue to work. This archive is separate from the normal namespaced library for new contributions.

The [original evidence](original/) contains the six requested checkpoints and their recursively linked receipts, build logs, expanded-statement sources/outputs, source records and AI reviews. Each copied artifact has an origin-to-public-path mapping and hash in the manifest. Historical absolute compile commands and workspace paths remain inside original receipts because rewriting them would invalidate the requested original hashes. These paths are historical provenance, not instructions to run on another machine. No agent conversations, private prompts, credentials, full-text papers, or historical compiled project objects are included. Original AI reviews retain their original wording and do not constitute human review.

| Requested checkpoint | SHA-256 |
|---|---|
| R02_GRAPH_TO_FACTORIAL_ROOT_CHECKPOINT_v1.json | `c26ccc356230306f362a71079907e963574e844fe5dbdd30d779e8c7d6aa331d` |
| LOCAL_WEAK_GRUSHIN_RAW_FACTORIAL_CHECKPOINT_v1.json | `4e98a5f84c6b82ec683c1a809582969b869ada06695c17775534b39ff1d1941b` |
| COULOMB_KS_PHYSICAL_FACTORIAL_CHECKPOINT_v1.json | `6e3d16e6c823f420c644eecffade7f5fc9763eef447812d0cc111095875e02a7` |
| COULOMB_SPIN_GROUND_PHYSICAL_POINTWISE_CHECKPOINT_v1.json | `94e82e50419c8febe9e7c7e36978f0651e0e4a16a3643c5d13a453a9a310dd88` |
| COULOMB_SPIN_GROUND_ANALYTIC_DESCENT_CHECKPOINT_v1.json | `6ee0000b29e3bf1c1508d13f054d859c7b006d3b6df7b252f160b99d59b08d02` |
| PHYSICAL_KS_ANALYTIC_DESCENT_SURJECTIVITY_CHECKPOINT_v1.json | `327568ba837f1ef07fa0e75809754ec26f51839dc619afc340d07b39f8cb2a7a` |

All requested endpoint sources match their sealed checkpoint hashes. All referenced continuation files were located. Two older development build receipts refer to earlier source revisions whose recorded hashes differ from the available source bytes: `PowerSeriesDiagonalInvariance_v1.lean` (`778d0c50...` versus available `80f9c0b1...`) and `KSSpectatorHomogeneousReconstruction_v1.lean` (`fcba187d...` versus available `01d868b9...`). Their receipts are preserved unchanged; the manifest records both full hashes. These earlier revisions were not recovered and must not be represented as reproduced. The clean rebuild uses the explicitly recorded available sources, also identified by later strict audit receipts. Historical references outside this continuation package are recorded separately, without recursively republishing the private freeze or unrelated research.

## Reproduce

Use Python 3.9 or later, the exact [Lean toolchain](lean-toolchain), and all nine dependency revisions in [dependency-pins.json](dependency-pins.json). Mathlib is pinned to `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`. From a clean committed repository checkout, obtain the repository's pinned third-party dependencies as described in [local verification](../../docs/local-verification.md), then run:

```sh
python3 tools/verify_rung2_recovery.py --check-only
python3 tools/verify_rung2_recovery.py \
  --lean /path/to/lean-4.34.0-rc2/bin/lean \
  --packages lean/.lake/packages --jobs 4
```

The runner starts with a new, empty `.local-ci/rung2-.../build` directory. It compiles every local module from source in dependency order and constructs `LEAN_PATH` from only that new output and the pinned third-party libraries. It does not read existing foundation or continuation project objects. Official Lean compiler/core binaries and pinned third-party compiled library artifacts are reused; this is a clean rebuild of the **local project closure**, not a rebuild of Lean or Mathlib from source.

It then prints complete expanded statements and axiom reports for every public declaration in all 409 recovered continuation modules, using the original conservative declaration-discovery helper. It rejects missing reports, nonstandard axioms, printer omissions/fallbacks, source changes, closure gaps, forbidden verification shortcuts and checkout changes. Every invocation records its exact tested Git commit/tree, commands, pins, source/object/log hashes and outcomes in a fresh receipt. No status is reported to GitHub by this runner. The repository's ordinary full verification remains a separate check.

## Current mathematical checkpoint

The recovered encoded chain covers genuine local weak Grushin weighted L2 factorial bounds, physical scalar/full-spin KS transport, pointwise/Taylor analyticity, and physical-coordinate analytic distance descent. The generic scalar endpoint explicitly assumes an actual Coulomb eigen-graph and a continuous locally Lipschitz a.e. representative; the full-spin/ground consumers supply their stated physical data. The two-electron ground theorem retains `Z > 0` and `32 < 9 * Z^2`. The descent identity concerns the literal normalized `originScaledDifference`, with its stated scale, chart and neighborhood restrictions. Noncomputable series and existential constants do not provide an executable coefficient algorithm.

Remaining obligations include mixed derivative estimates for the descended A/B series, compatible germs across charts, complete collision/intersection and exterior coverage, global H2 approximation by the specified dictionary, physical moments, rational solver correctness/termination, and operational bit complexity. The historical September 10 status and every original receipt remain unchanged. Successful replay checks the encoded statements; it does not supply a human definitions audit or establish the remaining global claims.

Frozen provenance: relative path `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, private historical commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The hash was checked against the original freeze manifest and artifact. The private commit/tag are not claimed to be public refs.

Recovery assistance: OpenAI Codex, GPT-6. No independent human mathematical review is claimed. Historical model identifiers are left as recorded or unknown.
