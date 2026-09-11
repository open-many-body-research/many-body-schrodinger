> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Two-center lower-bound execution checkpoint

The strongest new analytic statement is the separation-aware form inequality
proved in TWO_CENTER_IMS_v1.md. For one electron and two positive charges it
gives a certified lower energy from a finite rational scalar supremum bound.
The linear-partition corollary gives

    -z_max^2/2-z_max/d-pi^2/(32d^2) <= E_el <= -z_max^2/2,

where 2d is the nuclear separation. The implementation uses the stronger
finite partition family to improve two previously emitted molecular stages.
This is a paper continuum result with exact rational computational evidence,
not a Lean theorem or formal verification of Python.

## Actual electronic intervals

| Input, separation 2 | Replayed electronic interval |
| --- | --- |
| H2+, charges 1 and 1 | [-60603190564051/35184372088832, -68998015/134217728] |
| Charges 2 and 1, one electron | [-107848764024675/35184372088832, -8400385/8388608] |

The old lower endpoints were -2 and -9/2. Both upper endpoints come from the
sealed physical occupation-matrix stages; the combine operation fully
replayed those stages before intersecting with the new lower bounds.
`two_center_improvement_summary_v1.json` records exact old/new widths,
their exact differences, and diagnostic percentages. Its additional total
energy intervals add the exact nuclear constants 1/2 and 1, respectively;
those derived endpoints do not rely on decimal reference energies.

Each scalar certificate uses 1024 cells and 48 arithmetic bits. H2+ uses
a=-9/200,b=0; the unequal-charge input uses a=-1/20,b=-3/20. The finite
parameter comparisons are recorded in three separate JSON search receipts.
They propose parameters only; no optimality theorem or convergence of this
partition family to the actual energy is claimed. Scalar generation took
9.743786459 seconds for the first H2+ call and 1.200686833 seconds for the
unequal-charge call with shared in-process memoization. Fully replaying the
old upper stage during combination took 95.57689775 and 12.025307875 seconds.

## Verification and runtime

The four test groups check special trigonometric values, cosine/partition
constraints, the known exact linear-partition supremum, irrational nuclear
separation, replay and tamper rejection. All pass. The source-only isolated
replay copies the required Python sources and inputs to a fresh temporary
directory, compiles the source, runs these tests, rechecks both scalar
certificates, regenerates and checks the unequal-charge strengthened stage,
and rejects a modified lower endpoint. It passes in 53.193863791 seconds.
No compiled or persisted arithmetic cache is imported; within-process
memoization is used and disclosed in the receipt.

Generation used Homebrew Python 3.14.7. Independent source-only replay used
the bundled Python 3.12.14 interpreter at
`~/.cache/codex-runtimes/codex-primary-runtime/dependencies/python/bin/python3`.
Both produce the same exact rational claims. A fresh bundled-runtime check
of both scalar certificates took 11.34837275 seconds with peak resident
memory 31,506,432 bytes, including parsed certificates and in-process caches.
The receipts are `isolated_two_center_ims_replay_v1.json` and
`two_center_scalar_runtime_checks_v1.json`.

Homebrew Python intermittently stalled while its import machinery created
the standard-library `resource` and `_bisect` extension modules, before
interval arithmetic. Guarded traceback probes located those imports; the
initial stalled command was interrupted, and subsequent read-only process
inspection found no leftover computation. A fresh standalone import later
succeeded. Switching to the bundled interpreter resolved the execution
block; all source-only checks above then passed. This is an observed
environmental import failure, not a mathematical or source-compilation
failure. Its cause was not diagnosed beyond the captured import stack.

The root independently reviewed the complete scalar source and initial
mathematical argument in `../../audits/TWO_CENTER_IMS_ROOT_REVIEW_v1.md`.
The general linear-partition dissociation corollary was then separately
checked by root; the final proof hash is recorded in the new reconciliation
review. Review agreement does not replace the stated continuum proof or
amount to kernel verification. The checker shares rational primitives with
the producer; this common implementation remains part of the trust boundary.

## Preservation and next obligation

No earlier source, proof, certificate or seal was changed. The predecessor
seal is MOLECULAR_SEALED_MANIFEST_v1.json, SHA-256
1d37b073eb2c18f4a2f4bd9735fe7b2272b705da12ed4c0f0fef9417ce2ef3a0.
Frozen baseline: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660,
tag theorem-t-proof-freeze-2026-09-09; original
THEOREM_T_FREEZE_2026-09-09_212604/TWO_ELECTRON_THEOREM.md has SHA-256
7cec37a2d36509a8de2f0a09b4e3ca501879ab7928d4a7987dd87f8160cfbb79.

The next active computation is a cheap requested-precision algorithm for
the precisely separated one-electron/two-nucleus class implied by the
linear-partition corollary. It will be a separate version and will state
its exact acceptance condition and operational input-size cost. Formal IMS,
the translated molecular operator/form bridge and verified implementation
remain independent obligations.
