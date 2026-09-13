# Start contributing

This is a shared research record for the electronic many-body Schrödinger equation. People can work on separate pieces, reuse established results, and submit evidence for review. The complete many-body problem and the program's Theorem T remain open.

## Find work that fits your skills

Read the [README](../README.md), then [STATUS](../STATUS.md) and the [sector map](sectors.md). Each sector README names open problems and expected deliverables. Follow a claim ID to its statement card to see its exact hypotheses and limitations. The registry records formal proofs, conditional certificates, proposals, open problems, and withdrawals separately.

You can contribute a Lean formalization, an exact checker, a paper proof, a counterexample, a careful review, a reproducibility fix, or clearer documentation. Start with a narrow issue. LLM users should read [AGENTS.md](../AGENTS.md) and give their assistant the relevant claim card and contribution rules.

## Coordinate, then work in your own copy

1. Search existing issues and PRs for the problem ID. Open a **Claim a problem** issue or discuss the approach in Discussions. A claim coordinates work; it does not grant exclusive ownership.
2. Fork the repository through GitHub, clone your fork, and create a topic branch. Use current `main` for the corrected build; the original `v1.0-foundation` tag preserves its historical packaging.
3. Read [CONTRIBUTING](../CONTRIBUTING.md). Put new results in new files and use an erratum for a correction. Do not edit the frozen foundation in place.
4. Make one coherent change. If it changes a scientific claim, update its registry entry, evidence, and required statement card. Documentation and tooling fixes need not invent a claim ID.

## Check and submit

Install the pinned dependencies described in [local verification](local-verification.md). Review and commit your changes with an honest DCO sign-off (`git commit -s`) using your chosen public identity. Do not falsely add sign-offs for other people. The runner requires a clean, committed checkout. From the repository root, use:

```sh
python3 tools/verify_local.py --trusted-checkout --mode quick
```

A quick run helps during development; the maintainer runs the full suite before an ordinary merge. Lean contributions should also build locally. Push the tested branch to your fork and open a PR against this repository's `main`.

Fill in the PR template: what changed, evidence, assumptions, tests, human contributors and proposed credit split, and each person's AI usage. State `none` if no AI was used, or `unknown` if the history is not known. A tool/model is attribution, not proof of correctness.

## What happens next

The owner currently controls all merges. Reviewers can comment without write access. Maintainers review code before executing it, inspect DCO and disclosures manually, run full local verification, and assess the mathematical meaning of the statement. Changes requested in review stay in your branch. Further commits invalidate prior approvals.

After acceptance and merge, the attribution is recorded in a follow-up PR and appears in the [contribution dashboard](../CONTRIBUTORS.md). Dashboard percentages cover recorded accepted PR credit only; they are not a measure of the fraction of the science solved. [Governance](../GOVERNANCE.md) explains the owner's administrative exception and how authority may be delegated.

Your fork and PR do not modify the official files. Opening a PR does not automatically run your code on a maintainer's computer. Corrections remain traceable through Git history, protected version tags, errata, and new result versions.
