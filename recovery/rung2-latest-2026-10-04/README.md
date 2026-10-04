# Latest recorded Rung 2 sources, recovered 2026-10-04

This extends the [initial requested checkpoint recovery](../rung2-2026-10-04/README.md) through the later sealed local work recorded on September 11. It supplies the source files needed to resume the actual recorded stage, including derivatives, within-chart compatibility, scalar-ground symmetry/decay, SO2 axis descent and the completed distance-geometry components. It addresses [issue #6](https://github.com/open-many-body-research/many-body-schrodinger/issues/6) without changing any mathematical claim or evidence tier.

The [manifest](MANIFEST.json) records 1,292 local modules: 750 unchanged published foundation modules and 542 original continuation modules. Compared with the initial recovery, this adds 133 continuation modules. The package retains all original flat names, source bytes and checkpoint bytes. It includes 2,213 linked historical evidence records, mapping each origin to its public path and SHA-256. All six originally requested checkpoints and their hashes are retained. Twelve checkpoint files and the final focused axis-domain review seed the historical evidence closure.

As in the initial package, the two earlier intermediate revisions of `PowerSeriesDiagonalInvariance_v1.lean` and `KSSpectatorHomogeneousReconstruction_v1.lean` were not recovered. Their earlier build hashes, available source hashes, and later matching checkpoint/audit hashes are recorded explicitly. No referenced continuation file is missing. Original compiled project objects are deliberately excluded. Historical references outside this continuation recovery are separately identified; they do not imply publication or verification of the entire private freeze.

Original receipts retain historical absolute paths and compile/audit commands so their SHA-256 hashes remain valid. These historical paths are provenance and must not be copied into a new user's execution environment. No private prompts, agent conversation logs, credentials or full-text papers are included. The original AI reviews are historical assistance, not independent human mathematical reviews.

## Reproduce this snapshot

From a clean committed checkout, with the pinned Lean 4.34.0-rc2 executable and the repository's pinned third-party package libraries:

```sh
python3 tools/verify_rung2_latest.py --check-only
python3 tools/verify_rung2_latest.py \
  --lean /path/to/lean-4.34.0-rc2/bin/lean \
  --packages lean/.lake/packages --jobs 6
```

See [local verification](../../docs/local-verification.md) for obtaining the third-party dependencies. All nine revisions are recorded in [dependency-pins.json](dependency-pins.json); Mathlib is `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`. The latest wrapper uses the same recovery runner and the original declaration-discovery helper, with this manifest as its input.

Every local module is compiled from its exact source into a new, initially empty output directory. `LEAN_PATH` contains only the fresh local output and the pinned third-party library artifacts. No historical foundation/continuation project objects or incremental snapshots are imported. The official Lean compiler/core and third-party compiled library artifacts are reused; Lean and Mathlib themselves are not rebuilt from source.

The runner performs complete expanded-statement and axiom audits of all 2,205 public declarations in all 542 recovered modules. It checks report completeness and rejects nonstandard axioms, printer omissions/fallbacks, forbidden verification shortcuts, missing imports, source changes and checkout changes. Each run records its exact tested commit/tree, pins, commands and source/object/log hashes under a new `.local-ci/rung2-.../` directory. The ordinary repository full suite is separate from this clean source-closure replay.

## Current mathematical checkpoint

The requested initial chain supplies actual local weak Grushin weighted L2 factorial bounds, actual scalar/full-spin KS transport, pointwise/Taylor analyticity and physical-coordinate A plus distance times B descent. The restored later sources additionally contain:

- Complex and real coordinate mixed derivative bounds for the literal descended A/B series on the specified quarter polydisc. These do not differentiate the singular distance-times-B factor or silently change to operator-norm derivative bounds.
- Uniqueness and compatibility of A/B coefficients between centers within a fixed nuclear chart or within the pair chart. This does not identify coefficients across different chart types.
- The same scalar ground representative's reality, exchange/rotation symmetry, H2 exterior decay, pair evenness and bounded holomorphic SO2 axis descent. The latest scalar-ground axis theorem explicitly assumes `Z >= 2`. Earlier full-spin ground theorems retain `Z > 0` and `32 < 9 * Z^2`.
- Nuclear real distance representatives and their axis connection, the real axis-domain prerequisites, pair-distance algebra and collinear polynomial deviation bounds. These are completed components, not a finished distance-germ assembly.

The physical identity concerns the original normalized `originScaledDifference`, with its scale, chart, center and neighborhood restrictions. Existential constants, infinite sums and polynomial constructions remain noncomputable mathematical objects; no effective coefficient algorithm is supplied.

Remaining work includes the actual ambient distance-coordinate analytic germ composition and reconstruction, compatibility across different charts and collision strata, uniform estimates at noncollision centers, complete collision/intersection and exterior coverage needed for the approximation theorem, and global H2 approximation by the specified dyadic dictionary. The already restored H2 decay theorem does not discharge all exterior analyticity or dictionary-tail obligations. Physical moments, rational solver correctness/termination, operational bit complexity, Rung 2 and Theorem T remain open. The claims registry remains authoritative.

Frozen provenance: `rwa_proof/THEOREM_T_COMPOSITION.md` within `THEOREM_T_FREEZE_2026-09-09_212604/`, SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, private historical commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. The manifest and original bytes were checked without changing the snapshot. These private identifiers are not claimed as public refs.

Recovery assistance: OpenAI Codex, GPT-6. No independent human mathematical review or evidence-tier promotion is claimed. Historical model identities remain as recorded or unknown.
