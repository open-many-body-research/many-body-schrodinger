# Governance

## Roles

| Role | Who | Can |
|---|---|---|
| **Maintainer** | Members of the maintainers team | Merge to `main`, promote claim tiers, cut releases, and invite sector leads |
| **Sector lead** | Contributors with a record of accepted work in a sector, invited by maintainers | Required reviewer for their sector's paths (through `CODEOWNERS`); can label and triage issues in that sector |
| **Reviewer** | Anyone | Submit a review record under `reviews/`. Two independent human `ACCEPT` records support a maintainer-approved promotion to P2 |
| **Contributor** | Anyone | Fork, open issues and PRs, claim problems, and join Discussions |

Nobody gets write access just by contributing or earning contribution credit. The repository owner controls invitations and permissions. Reviewers can help without receiving write access. The owner is currently the sole maintainer; adding members to the code-owner team delegates approval authority to those members.

## How `main` is protected

GitHub rulesets enforce the ordinary contribution workflow. Repository administrators retain a pull-request-only bypass for owner-authorized maintenance; this is an exception to the review and status requirements below, not permission for contributors to bypass them. Administrators can also change repository settings. The owner is currently the only administrator.

- **No direct pushes.** All changes arrive by pull request.
- **Reviews.** Every pull request needs at least one approving review from a code owner. That approval is dismissed if new commits are pushed afterwards. Changes to the trusted definitions (`lean/**/Spec/**`), verification infrastructure, tools, or governance files need maintainer approval.
- **Required machine check.** The single required GitHub status is `local/verify`. A maintainer starts the [local runner](docs/local-verification.md) on a reviewed commit. Its full run checks foundation hashes, the Lean build and source policy, the axiom audit, registry and status-page consistency, contribution records and dashboard consistency, and all certificate checkers including the independent algebra audit. GitHub Actions is disabled.
- **Human checks.** Maintainers inspect DCO sign-offs, contribution credit and AI disclosures, and the mathematical meaning of statements. DCO and the truth of attribution are not automatically verified by the local runner.
- **History.** Force-pushes and branch deletion are blocked, and history must stay linear.
- **Tags.** Release tags (`v*`) can't be moved or deleted.
- **Fork PRs.** Opening a PR does not execute its code. Maintainers review it before manually running checks; unfamiliar code must run in a disposable isolated environment without account credentials. The local runner is not a sandbox.

## Promoting a claim

1. The author opens a PR that adds the claim with the tier its evidence supports.
2. Maintainers run the local verifier on the reviewed commit and record its machine-check results as `local/verify`. GitHub Actions is disabled.
3. A code owner checks what machine checks cannot establish: the **statement card**, especially whether the definitions are faithful and whether all premises are listed.
4. For P2 claims, the two review records must come from people independent of the author.
5. If the PR raises a sector's "current best", a maintainer updates the sector README and the changelog.

## Disputes and errors

- **Reporting a mistake.** Anyone who believes a merged claim is wrong opens a **"Report an error"** issue.
- **Triage.** Maintainers aim to triage it within 14 days.
- **Confirmed errors.** An erratum is added in `errata/`, and the claim is downgraded (often to X) in the same PR. Downstream claims that depend on it are downgraded too.
- **No deletions.** Wrong claims are never deleted, only marked. The public record of what was wrong is part of the project's value.
- **Disagreement over a definition or a tier.** Maintainers decide by majority. When in doubt, choose the lower tier.

## Releases

- `v1.0-foundation` is the frozen baseline.
- Later releases (`v1.1`, `v1.2`, …) are cut by maintainers when a set of new claims has settled.
- Every release has a changelog entry listing new claims, promotions, and errata.

## Changing these rules

Only maintainers can change governance, contribution rules, or verification policy, through a PR that stays open for public comment for at least 7 days. Rules can be tightened immediately, but loosening them always needs the comment period.
