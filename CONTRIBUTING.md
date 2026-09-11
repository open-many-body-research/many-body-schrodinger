# Contributing

This repository collects results about the electronic many-body Schrödinger equation. Anyone can fork it, open issues, and send pull requests. Only maintainers can merge to `main`. Every merged result carries an **evidence tier**, and the tier is what makes it usable by other people.

The rules are strict for one reason: if an unverified claim gets into the record, everything built on it becomes unreliable. A claim here is only worth as much as its evidence.

---

## 1. Evidence tiers

Every result in [`claims/registry.yaml`](claims/registry.yaml) has exactly one tier.

| Tier | Name | What counts as evidence | Can other results depend on it? |
|---|---|---|---|
| **L** | Lean-verified | Lean 4 source that builds in CI against the pinned Mathlib. No `sorry` or `admit`, no new `axiom`s, and none of the other forbidden constructs in §3. `#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`. Plus a reviewed **statement card** (§4). | Yes, including other L results. |
| **C** | Certified computation | An exact or interval-arithmetic certificate (rationals, dyadics, or outward-rounded intervals). It needs a separate **checker** that recomputes it from the published inputs, and CI must run that checker. Floating-point results never count as certificates. The mathematical reduction from the certificate to the claim must be at tier L or P2, or be listed under `conditional_on`. In that case the claim is reported as *conditional*. | Yes. |
| **P2** | Reviewed paper proof | A complete human-readable proof in `proposals/` plus **two independent review records** in `reviews/`. Reviewers must not be the author and must not be listed as the author's co-authors. | Yes, but anything depending on it can be at most P2. |
| **P1** | Unreviewed paper proof | A complete written proof that hasn't had two independent reviews yet. | No. It's a proposal. |
| **N** | Numerical evidence | Reproducible floating-point computations: the script, pinned environment, raw output, and hardware notes. | No. It's evidence, not proof. |
| **O** | Open / conjecture | A precisely stated problem or conjecture, with the known partial results. | No. |
| **X** | Withdrawn | Found wrong, vacuous, or superseded. The entry stays in the registry with a link to its erratum. | No. |

**Tiers only move up with new evidence.** To go from P1 to P2 you need reviews. To go from P2 to L you need a formalization. A result's tier can never be higher than the lowest tier of anything it depends on.

## 2. The v1.0 foundation is frozen

The `v1.0-foundation` tag marks the baseline that everyone builds on. Files that existed at that tag are **append-only in spirit**:

- Don't silently change a proof, certificate, statement, or number in an existing file.
- To fix something, add an erratum in `errata/` (use `errata/TEMPLATE.md`) and change the registry entry's tier or status in the same pull request.
- A new version of a result goes in a new file (`..._v2.md`, `FooV2.lean`) that cites the one it replaces.

Tags are protected and can't be moved or deleted.

## 3. Rules for Lean contributions (tier L)

- **Toolchain.** Use the versions pinned in `lean/lean-toolchain` and `lean/lake-manifest.json`. Toolchain bumps are separate maintainer-only PRs.
- **Forbidden in `lean/`.** CI enforces all of these (`tools/lean_policy.py`):
  - `sorry` and `admit`
  - `axiom` declarations
  - `native_decide`, `implemented_by`, `@[extern]`, `unsafe`
  - `debug.skipKernelTC` and any `set_option` that weakens kernel checking
  - `opaque` constants that stand in for real mathematics
- **Axiom audit.** Every declaration listed under a tier-L claim is checked with `#print axioms` in CI (`tools/axiom_audit.py`). The only allowed axioms are `propext`, `Classical.choice`, and `Quot.sound`.
- **Definitions matter more than proofs.** A Lean proof only shows that the *stated* theorem follows. If the Hamiltonian, domain, or spin space is defined wrong, the proof is worthless. So:
  - **Trusted definitions.** These live in `lean/Foundation/`: `ContinuumFoundation_v1` (spaces, antisymmetry, potential, weak derivatives, $H^1$ and $H^2$), `CoulombOperatorCore_v2` (the operator), `CoulombH1Form_v1` (the form), `UnboundedResolvent_v2` (spectrum), and `CoulombSpectralFoundation_v3` (the ground energies). Any new `lean/ManyBody/Spec/` directory is trusted too.
  - **Reuse, don't redefine.** A new theorem should import these definitions rather than define its own copy of "the Hamiltonian".
  - **Approval.** Changes to `lean/Foundation/**` or `lean/**/Spec/**` need maintainer approval (see `.github/CODEOWNERS`), and they are frozen as described in §2.
- **Premises must be explicit.** If a theorem takes a hypothesis that hasn't been proved (for example "assume this form comparison holds"), the statement card must say so up front. The claim is then recorded as *conditional* on that hypothesis.
- **Where new work goes.** New modules go under `lean/ManyBody/<Sector>/…` with namespaced module names (`ManyBody.S3.HeliumMoments`). The `ManyBody` library is already declared in `lean/lakefile.toml`. Keep each module's public statement short, and put helper lemmas in `…/Internal/` files.

## 4. Statement cards (required for tiers L, C and P2)

Each claim needs a statement card at `claims/cards/<ID>.md`, based on `claims/cards/TEMPLATE.md`. The card gives:

1. The exact formal statement: the Lean declaration name, or the certificate's input and output.
2. A plain-English statement a physicist or analyst can read.
3. A list of **every hypothesis**, marked *proved* (with a link) or *assumed*.
4. A **definitions audit**: why the objects in the formal statement really are the physical ones. For example: "`coulombPartialOperator N Z` is the operator whose graph is $\{(\psi, -\tfrac12\Delta\psi + V\psi)\}$ with $\psi$ in weak-$H^2$ antisymmetric $L^2((\mathbb R^3 \times \{\uparrow,\downarrow\})^N)$".
5. What the result **does not** show.

A reviewer who can't check item 4 from the card can't approve the PR.

## 5. Rules for certificates (tier C)

- **Exact arithmetic only.** Use rationals, integers, dyadic intervals with explicit outward rounding, or a verified interval library. Floating point may be used to *find* a certificate but never to *check* one.
- **Separate checker.** The checker lives in `certificates/<name>/check*.py` (or a Lean program). It reads only the published inputs and must not import the code that produced the certificate. Anything else, including search and optimization scripts, is untrusted.
- **CI runs it.** Every certificate has a CI job. If a full check takes more than 30 minutes, add a reduced check that runs on every PR, and run the full check on the scheduled workflow.
- **Record hashes.** Record the SHA-256 of every input and output file in the certificate's `MANIFEST.json`.
- **Anonymize.** Leave out hostnames, usernames, and absolute paths from certificate metadata.

## 6. Rules for paper proofs (tiers P1 → P2)

- **Where.** Submit to `proposals/<sector>/<short-name>.md`. LaTeX (`.tex`) with a compiled PDF is also fine.
- **Complete.** The proof must be complete: no "it is easy to see" for a step that actually needs work. Every cited external result needs a precise reference (theorem number, page) *and* the hypotheses under which you use it.
- **Reviews.** A review goes in `reviews/<claim-ID>/<reviewer-handle>.md`, based on `reviews/TEMPLATE.md`. The reviewer states what they checked line by line, what they didn't check, and a verdict: `ACCEPT`, `ACCEPT-WITH-CORRECTIONS`, or `REJECT`. It takes two `ACCEPT` reviews to promote a claim to P2.
- **Adversarial review is welcome.** A review whose only goal is to break the proof is exactly what the process needs.

## 7. AI assistance

AI tools are allowed and were used heavily to build the v1.0 foundation. They're also the main reason these rules exist. AI systems produce fluent, confident, and sometimes vacuous or wrong mathematics, so:

- Say so in the PR template if AI tools produced substantive content.
- An AI-generated paper proof is P1 until two humans review it, just like any other proof.
- An AI-generated Lean proof is fine, because the kernel checks it. The statement card, though, must be written or checked by a human.
- Theorem counts don't matter. Fifty scalar lemmas are not a result. Group work by what it establishes about the physical problem.

## 8. Working on a sector

The problem is split into **sectors** (see [`docs/sectors.md`](docs/sectors.md)). Each sector has a README with open problems. Each problem has an ID such as `S3.2`, a checkable deliverable, and the current best result.

1. **Pick a problem** and open an issue with the **"Claim a problem"** template. That tells others you're working on it, so work isn't duplicated. Claims expire after 60 days without activity. Nobody owns a problem outright, and parallel attempts are allowed once a claim has been announced.
2. **Discuss your approach** in the issue or in GitHub Discussions before investing heavily.
3. **Send the pull request.** It should:
   - update `claims/registry.yaml`,
   - add the statement card,
   - add the evidence,
   - update the sector README's "current best" line if the result improves it.

## 9. Pull request checklist

- [ ] One logical result per PR.
- [ ] Every commit is signed off (`git commit -s`) under the [Developer Certificate of Origin](https://developercertificate.org/). This certifies that you have the right to submit the work under this repository's licenses.
- [ ] `claims/registry.yaml` has been updated, and `python3 tools/validate_registry.py` passes.
- [ ] For Lean changes, `lake build` and `python3 tools/lean_policy.py` pass locally.
- [ ] For certificates, the checker runs from a clean checkout.
- [ ] No personal paths, hostnames, credentials, or copyrighted full-text papers. Cite papers instead of including them.

## 10. Licenses

- **Code and Lean sources** are licensed under [Apache-2.0](LICENSE).
- **Text, proofs, and documentation** are licensed under [CC BY 4.0](LICENSE-DOCS).

By contributing, you agree that your contribution is licensed under the same terms.
