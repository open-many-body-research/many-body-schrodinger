# Contribution credit and AI attribution

[CONTRIBUTORS.md](../CONTRIBUTORS.md) is generated from accepted records in `records/`. GitHub's commit and line counts do not capture reviews, shared authorship, or scientific value, so this project uses an explicit accepted-PR ledger.

## What a percentage means

Every recorded merged PR contributes exactly **one credit**, divided among its human contributors. A contributor's share is their credits divided by all recorded PR credits, multiplied by 100. A 50/50 collaboration earns 0.5 credit each. No credit is awarded merely for commits, generated lines, issue comments, an unmerged PR, or an LLM response.

The dashboard shows overall shares and separate totals for `research`, `review`, `documentation`, and `infrastructure`. One primary category per PR prevents double counting. A small typo fix and a major theorem each count as one accepted PR: this measures participation in accepted work, not effort, correctness, scientific importance, ownership, financial entitlement, or the percentage of the many-body problem solved. Maintainers may ask contributors to combine artificially fragmented PRs. Rounded percentages can differ slightly from 100%.

**Coverage:** the initial foundation import and pre-ledger work are excluded. Their human/model breakdown was not reliably recorded and must not be invented. The dashboard is not a complete historical attribution of the project. New merged PRs appear after a maintainer accepts their record in a follow-up PR; recording is manual, not an automatic GitHub webhook. No GitHub Actions are used.

## Contributors: propose your attribution

In the PR template, name each human contributor by public GitHub handle and propose a split that totals 100%. Use public handles only; no email or legal name is required for this ledger. The maintainer confirms the split with the contributors before recording it. Disputes are handled in the PR or an issue and corrected transparently.

For each person, declare AI assistance as `used`, `none`, or `unknown`. If used, list **every substantive tool** with provider, tool/product, model/version if known, and role (for example implementation, proof search, editing, or review). Use JSON `null` when the exact model was not recorded. Never infer a model from prose or equate an AI review with an independent human review. LLMs do not receive a human credit percentage; they are tools attributed alongside the responsible person. Tool use is self-reported, not technically verified by this system.

## Maintainers: record an accepted PR

After the source PR has merged, create `records/PR-000123-v1.json` in a separate attribution PR using [the template](record-template.json). Replace all placeholders. `merged_commit` and `merged_at` must exactly match GitHub's merged PR metadata. Do not credit a pending PR, including the attribution PR itself, in anticipation of a merge.

`credit_bps` is an integer split of the PR's one credit in 10,000 parts: 10,000 = 100%, 5,000 = 50%. Every record must total exactly 10,000, with positive shares and one entry per human. `ai` contains exactly one declaration per contributor. Set `tools` to an empty list for `none` or `unknown`; `used` requires at least one named tool and its role.

```sh
# Validate records and confirm every source PR is actually merged (requires authenticated gh).
python3 tools/contributions.py --verify-github
# Generate the dashboard after adding a record.
python3 tools/contributions.py
# Check records and the generated dashboard without changing files.
python3 tools/contributions.py --check
# Confirm existing records were not edited or deleted relative to a reviewed base.
python3 tools/contributions.py --check --base origin/main
```

Refresh the base ref before reviewing a PR. `--verify-github` checks source PR state, merge commit, and merge timestamp; it cannot validate the truth of co-authorship, credit splits, or model disclosures. Maintainer review is required for those. The offline local runner checks the schema and generated dashboard, not live GitHub metadata. Review changes to this checker as carefully as ledger changes.

## Corrections preserve the record

Never edit or delete an accepted record. Add the next version for the same PR, such as `PR-000123-v2.json`, set `supersedes` to `PR-000123-v1`, and explain the correction in `correction_reason`. Its complete replacement split and disclosures supersede the old attribution; the source PR remains the same. Versions must form one unbroken chain. Only the latest version counts, so a correction cannot award a second credit. Git history and the old records preserve the earlier account. The base-comparison check enforces unchanged prior record bytes when a base is supplied.

Missing attribution can be added later using the same review process. Do not backfill foundation contributions or unknown model names without evidence. Credit never grants merge access or changes an evidence tier. All ledger changes and generated dashboard updates require the owner's code-owner review under the repository's ordinary protection rules.
