> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Lean scope, builds, and reproducibility — audit version 1

This is a new post-freeze formalization. It does **not** prove Theorem T.

The frozen sources copied here are identified individually in
`frozen-source-provenance.json`, checked against `FREEZE_MANIFEST.json`. The
historical commit is `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`. The actual frozen directory in this checkout
is `THEOREM_T_FREEZE_2026-09-09_212604/`; the shorter directory name in the latest
request is absent. Frozen artifact bytes were unchanged. Earlier `git status`
checks refreshed some live, non-frozen dependency Git-index modification times;
all nine index SHA-256 values still match the frozen counterparts. No attempt
was made to restore timestamps. Future Git queries in the reproducibility
driver set `GIT_OPTIONAL_LOCKS=0` to suppress optional index refreshes.
The precise frozen paper targets and their SHA-256 values are also recorded in
`paper-target-provenance.json`.

## Exact verification boundary

`AtomicTwoElectron.lean` proves real scalar implications, a bound on a supplied
finite sum of natural-number stage costs, and a least successful index bound
given a successful witness. It contains no Coulomb operator, computed moments,
physical termination proof, Turing machine, or bit-cost implementation. In
particular `Nat.find` with an existence premise does not by itself implement the
desired terminating physical certifier. The frozen Lake configuration did not
list this module as a library or default target; this audit explicitly compiled
the source.

`TempleScalars.lean` proves finite weighted-sum and scalar interval statements.
`Temple.lean` connects such statements to an **actual finite-dimensional**
complex Hermitian operator. Its `[FiniteDimensional ℂ E]` hypothesis is visible
in the audited theorem statement. It supplies no continuum Temple theorem.
`Boundary.lean` proves scalar, finite-output, and explicit two-dimensional
quadratic-form statements. Its abstract variational-infimum perturbation lemma
requires the physical model-error premise; no continuum reduction is implicit.

All four verbatim source copies compiled with exit code 0. Their recorded
`#print axioms` output uses only `propext`, `Classical.choice`, and `Quot.sound`,
or no axioms. This establishes exactly those statements, not the missing
continuum premises.

## New continuum target

`ContinuumFoundation_v1.lean` uses actual Euclidean `R^(3N)` and complex L2
wavefunctions. `SpinSpace N` is the finite l2 sum over all `2^N` spin assignments
of these continuum L2 spaces, giving Lebesgue measure in space and counting
measure in spin. Coordinate permutations are real linear isometries; mathlib's
measure-preservation theorem makes their L2 pullbacks well-defined.

The fermionic submodule imposes permutation sign on simultaneous spatial and
spin exchange. `FermionicClosed_v1.lean` proves that submodule closed, as an
intersection of equality sets of continuous maps, and constructs its
`CompleteSpace` instance. The actual continuum fermionic space therefore has
both a verified complex inner-product-space instance and completeness.
`WeakPartial` tests complex-valued functions against every real
smooth compactly supported test function. `HasH2` requires all first and mixed
second distributional derivatives in L2. `targetDomain` is precisely this H2
condition on every spin component intersected with the fermionic subspace.

The Coulomb potential uses exact nuclear and pair distances and each unordered
electron pair once. The convention `0⁻¹ = 0` merely selects values on collision
sets; proving those sets null is still required before asserting that this
representative has the standard a.e. interpretation. There is no Coulomb
softening, bounded-domain cutoff, finite basis substitution, or assumed
self-adjoint-operator structure.

The Hamiltonian is specified by its weak-derivative **graph relation**.
Single-valuedness is proved through uniqueness of weak L2 derivatives, using
mathlib's theorem that equal integrals against all smooth compactly supported
tests imply a.e. equality. Existence of an image for every target-domain state,
linearity, and conversion to an actual unbounded operator remain separate
obligations. `LinearPMap` in mathlib is an available future operator target; this
audit does not claim mathlib lacks unbounded-operator infrastructure.

`variationalGroundEnergy` is the EReal infimum of the normalized graph numerical
range. Using EReal avoids falsely assigning a finite value to an empty or
unbounded set. This is a definition of the variational target, **not** a proof
that it is finite, attained, or equal to the bottom of a self-adjoint spectrum.

`ExactDictionary_v1.lean` defines the original exponential nodes `Z*2^j` and
factorial-scaled symmetric nonnegative distance monomials, with a single copy on
the diagonal `i=h`. The native degree rule is `2*j+i+h+k ≤ n`, equivalent to
`j ≤ floor(n/2)` and `i+h+k ≤ n-2*j`. The finite span is on the actual R6.
Multiplying columns by nonzero rational powers of two does not change that
real span used by the rational computation. Equivalence with a complex-linear
span for the physical ground-state problem is not proved. The canonical choice
of those powers, exact reduced moment identities,
and their computation costs are **not** formalized here. The L2 dictionary is
defined through a.e. equality to a spatial span member times the physical spin
singlet. The definition does not silently assert L2 or H2 membership.

`ThreeElectronSpin_v1.lean` proves that every three-electron spin assignment has
two equal spin labels and that every spin-only tensor alternating under all
electron permutations is zero. It uses the exact spin-1/2 factor of the
continuum space. This verifies a specific obstruction to transplanting the
two-electron spatial-symmetry/singlet construction; it does not determine the
lithium ground state's energy or spatial symmetry.

## Verified new structural theorems

- `fermionicSubspace_closed` and the `fermionicCompleteSpace` instance.
- `weakPartial_unique`, `h2_implies_h1`, and `scalar_graph_hasH2`.
- `scalar_graph_unique`, `hamiltonian_graph_unique`, and
  `graph_input_in_targetDomain`.
- `variational_ground_le_trial`, conditional only on an actual normalized
  state and graph pair supplied in its visible premises.
- `distances_exchange`, `generator_exchange`, `dictionary_exchange`,
  `exact_dictionary_nested`, and `trial_dictionary_nested`.
- `three_spins_repeat` and `no_three_electron_alternating_spin`.

These modules compile successfully without user mathematical axioms, `sorry`,
or `admit`. Their reported axiom dependencies are only the ordinary Lean
foundations `propext`, `Classical.choice`, and `Quot.sound`. The continuum energy
construction is noncomputable; no executable energy algorithm is defined or
verified here.

## Remaining load-bearing obligations

1. Collision-null-set proof, Coulomb multiplication bounds, Hardy inequalities,
   and existence of an L2 graph image on the entire H2 fermionic domain.
2. Graph linearity and a densely defined closed self-adjoint `LinearPMap`;
   agreement of its domain and action with these definitions, semiboundedness,
   and spectral/variational ground-energy equality.
3. Hydrogenic spectrum, the two-electron spectral separator, ground-state
   existence, positivity, simplicity, symmetry, and the unit-singlet embedding.
4. Dictionary columns in H2; exact normalization and moment formulas.
5. Uniform weighted analyticity, quantitative KS descent, all collision
   strata, global H2 approximation and graph residual bounds. A compiled
   definition or scalar implication proves none of these.
6. Continuum Temple certification with the actual unbounded operator and
   certified spectral separator.
7. Exact rational data representations, rounding, constant computation,
   rational matrix optimization, and an executable stopping loop.
8. Termination from discharged continuum estimates, plus a verified model
   counting individual Boolean/Turing operations (including representation,
   arithmetic, loop control, and output). The current scalar `stageCost`
   variable is not such a cost semantics.

For N=3 and variable N these obligations must be rebuilt; the definitions make
the dependence on N and Z explicit but provide no uniform regularity or
efficiency theorem. The approximation order is n, not N.

## Pinned environment and actual execution

Lean: `leanprover/lean4:v4.34.0-rc2`, compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`.

Mathlib: `d9ed2b07e3d851ae48dbfe62550f6da9a1c128c9`.
`lake-manifest.json` records the exact nine dependency commits. The recorded
dependency audit checks their HEAD revisions and that tracked source is clean.

The executed builds call the pinned Lean binary directly with a `LEAN_PATH`
containing only the new build directory and the existing dependency libraries.
All outputs go into this new directory. No Lake process runs in an old or
frozen directory. These are **source rebuilds of the listed project modules
against read-only pre-existing dependency oleans**. The dependencies were not
rebuilt from source or independently rechecked by a separate kernel.

`logs/legacy-build-results.json` contains exact commands and source hashes for
the successful four-module rebuild. `logs/pinned-dependency-audit.json` records
compiler identity, compiler-binary SHA-256, and dependency checks. Failed
development attempt logs are retained; `sorryAx` arising from Lean's error
recovery in a failed run is not a successful proof and must not be counted as
one. Final successful results are identified in `logs/final-build-summary.json`.

To reproduce against the same read-only local dependency cache, from the
workspace root run:

```sh
python3 THEOREM_T_POST_FREEZE_WORK/AUDIT_2026-09-09_v1/lean/rebuild_v1.py
```

Every invocation creates a fresh `lean/runs/<UTC timestamp>/` directory, so
completed logs and binaries are preserved. The original `build_legacy.py` is
retained as the historical initial driver; use `rebuild_v1.py` for new runs.

For an independent dependency-source rebuild, create a **new** directory under
`THEOREM_T_POST_FREEZE_WORK/`, copy the `.lean` files, `lakefile.toml`,
`lean-toolchain`, and `lake-manifest.json` there, install the pinned Lean
toolchain with its `ELAN_HOME` also inside that new directory, and run:

```sh
lake build
```

Honor the copied lockfile; do not run `lake update`. Do not run
`lake exe cache get` for that from-source experiment. Check the
resolved dependency commits against the supplied manifest and keep the full
build log. This expensive clean dependency build was **not performed** in this
audit; no clean-build result is claimed.
