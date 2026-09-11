# Governance

## Roles

| Role | Who | Can |
|---|---|---|
| **Maintainer** | Members of the maintainers team | Merge to `main`, promote claim tiers, cut releases, and invite sector leads |
| **Sector lead** | Contributors with a record of accepted work in a sector, invited by maintainers | Required reviewer for their sector's paths (through `CODEOWNERS`); can label and triage issues in that sector |
| **Reviewer** | Anyone | Submit a review record under `reviews/`. Two independent `ACCEPT` records promote a paper proof to P2 |
| **Contributor** | Anyone | Fork, open issues and PRs, claim problems, and join Discussions |

Nobody gets write access to `main` just by contributing. People earn it through a record of careful, verified work.

## How `main` is protected

These settings are enforced by GitHub repository rulesets, not by trust.

- **No direct pushes.** All changes arrive by pull request.
- **Reviews.** Every pull request needs at least one approving review from a code owner. That approval is dismissed if new commits are pushed afterwards. Changes to the trusted definitions (`lean/**/Spec/**`), CI, tools, or governance files need maintainer approval.
- **Required checks.** A PR must pass these before it can merge:
  - the Lean build
  - the Lean policy scan
  - the axiom audit
  - registry validation
  - the certificate checkers
  - DCO sign-off
- **History.** Force-pushes and branch deletion are blocked, and history must stay linear.
- **Tags.** Release tags (`v*`) can't be moved or deleted.
- **Fork PRs.** Workflows from forks run with read-only permissions and no secrets. A maintainer must approve them before they run.

## Promoting a claim

1. The author opens a PR that adds the claim with the tier its evidence supports.
2. CI checks everything that can be checked by machine.
3. A code owner checks the part that can't: the **statement card**, especially whether the definitions are faithful and whether all premises are listed.
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

Only maintainers can change governance, contribution rules, or CI policy, through a PR that stays open for public comment for at least 7 days. Rules can be tightened immediately, but loosening them always needs the comment period.
