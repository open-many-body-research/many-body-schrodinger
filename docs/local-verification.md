# Local verification service

GitHub Actions is disabled. Maintainers run `tools/verify_local.py` on a reviewed checkout and may report its result as a GitHub commit status. No server, subscription, webhook, Actions runner, or background execution of contributor code is needed.

## Run a check

Install Python 3.9 or later, PyYAML 6.0.2, Git, and the Lean toolchain pinned in `lean/lean-toolchain`. Put `lake` on PATH. Obtain the pinned dependencies with `cd lean && lake exe cache get` before the first full run. Do not update dependency revisions.

Start from a clean committed checkout that you have reviewed:

```sh
python3 tools/verify_local.py --trusted-checkout --mode quick
python3 tools/verify_local.py --trusted-checkout --mode full
```

The full run checks the foundation source hashes, registry, generated status page, Lean source policy, complete Lean build, every registry-listed tier-L declaration's axioms, all published certificates, and the independent algebra audit. A quick run omits the build/axiom audit and uses two reduced certificate checks; it cannot satisfy the full verification requirement.

Each run writes `.local-ci/<timestamp>-<commit>/summary.json` and individual logs. Receipts bind the outcome to the Git commit/tree and log hashes. These files are ignored by Git. Review logs for private paths or host information before sharing them; the runner never uploads logs automatically.

## Report to GitHub

With GitHub CLI already authenticated as an authorized maintainer:

```sh
python3 tools/verify_local.py --trusted-checkout --mode full \
  --report-status open-many-body-research/many-body-schrodinger
```

The commit must already exist on GitHub. The runner reports pending, then success, failure, or error using the `local/verify` commit status. Quick runs use a separate `local/quick` status. Only the commit identifier, status name, and generic outcome are sent. A dirty checkout, changed commit, failed step, or missing dependency cannot produce a success status. If status reporting fails, the local receipt records that failure and the command exits unsuccessfully.

The required `local/verify` branch protection status is configured separately on GitHub. A maintainer also checks each contributor's DCO sign-off and approves the result's statement card and mathematical meaning. A status is a maintainer's verification report, not cryptographic proof of execution or a substitute for review.

## Handling contributions

Do not automatically fetch and run outside pull requests on a personal computer. Review changes first, especially Python scripts, Lake configuration, dependencies, native code, and verification tools. Run unfamiliar code in a disposable isolated environment without account credentials. This runner is an orchestrator, not a security sandbox; the trust flag is an explicit operator acknowledgement.

When a PR is approved for verification, check out its exact head commit in the reviewed environment and run the full check there. The same command works on another maintainer-controlled machine. Changes to verification tooling require maintainer review. Foundation corrections remain append-only through errata and new source versions.
