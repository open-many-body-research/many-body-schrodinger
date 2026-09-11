> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Focused review of the next weak Grushin gain composition

Reviewed 2026-09-10. **No defect was found in the inspected sealed bridge
statements. They do not yet compose into a uniform local weak one-step gain
without the specific additional lemmas below.** This review concerns the new
integration boundary; it does not repeat the earlier broad continuum or local
elliptic audits. No Lean source was edited or recompiled for this review.

The three sealed checkpoints and their current hashes are:

| Checkpoint | SHA-256 |
|---|---|
| `GRUSHIN_PRELIMINARY_H2_SEQUENCE_CHECKPOINT_v1.json` | `0bff108fafaf9eb59501f006b08a87135ed85ef182cc01648a7f80c7566694c0` |
| `WEAK_GRUSHIN_CUTOFF_COMMUTATOR_CHECKPOINT_v1.json` | `e664a7d3ea38ee2b28a2f8cbade9bfe1009a40b7bb4f8a017cc1bccc66ce9f31` |
| `COMPACT_WEAK_GRUSHIN_LOCALIZATION_CHECKPOINT_v1.json` | `3f4264c8b015c9fc166f3d5da841b5ec2523b7140fd75adcd1e045a1d2a5544a` |

Their 16 source/object fingerprints and eight linked strict receipts were
rechecked. All receipts report successful compilation, complete standard-only
axiom reports, and no printer ellipsis; the recorded expanded-log hashes match.
The review read the exact final sequence, cutoff-output and local-output
sources, their relevant expanded hypotheses, and the actual jet/principal,
commutator, Caccioppoli and support definitions needed for this composition.
This is review evidence, not an independent implementation or a source rebuild.

The preliminary sequence has the quantifiers needed for regularity: for fixed
open `U`, compact `C`, and open `Ω` with `U⊆C⊆Ω`, there is one eventual threshold
after which the partial mollification is locally weak H² on `U` and satisfies
the weak equation for **every** compact test supported in `U`. This is stronger
than a separate threshold for each test and avoids that quantifier error.
Both actual global L² input sequences contract and converge strongly.
Preliminary second-derivative norms may grow with the mollification index.

The sealed commutator starts with a **global** L² input and genuine global
first and ordered second weak jets. Its output is a compact weak-H² cutoff
whose actual principal expression is

\[
P_c(\chi f)=\chi P_cf-C_Y(\chi,f)-c|y|^2 C_T(\chi,f).
\]

Every displayed localized term is L². The theorem supplies its actual L²
output and identifies it by all real compact smooth tests. It does not
assert that the uncut weighted principal expression is globally L².

The local-output Caccioppoli theorem still assumes a global compact weak-H²
input `f,d,e`, but needs its PDE only on an open set containing the energy
cutoff's support. It correctly identifies `principal c e=h` almost everywhere
there by local test-function uniqueness. The resulting integral pairing may
replace the principal expression by `h` because the cutoff vanishes outside
that set. No statement identifies the compact cutoff's entire output with
the uncut forcing alone; the commutator terms remain essential.

The concrete remaining composition obligations are:

1. **Local input to global L² extension.** The preliminary sequence accepts
   actual global L² classes `G,h`; a merely locally L² weak KS input does not
   meet that premise. A compact indicator extension of both raw functions,
   equal to them on a fixed compact set and preserving the PDE on an interior
   open set, is sufficient. Its proof must use support of `splitGrushin φ`,
   without differentiating the indicator. No such product Grushin wrapper was
   found in the inspected sources. Root has assigned this precise lemma for
   implementation after this review. A theorem initially restricted to global
   L² data may proceed before that local-data extension is complete.

2. **Local H² to one compact global jet system.** For each sufficiently large
   index, choose an outer smooth cutoff `ξ` equal to one on an open
   neighborhood of the later energy-cutoff support, and form `F_n=ξG_n`.
   `ProductLocalWeakH2On` supplies its global weak first and ordered second
   witnesses; choosing the second witnesses gives the full `Jet` required by
   the commutator. Compact support is an AE consequence of `F_n=ξG_n`.
   The draft `LocalWeakGrushinPlateau_v1` addresses this gap and transfers the
   PDE on the open plateau via `splitGrushin_zero_off_test`; its status is not
   upgraded by this review. Fix the geometric cutoffs and plateau sets before
   selecting the regularization threshold.

3. **Uniform quantitative bounds, not only L² membership.** The commutator
   checkpoint proves membership, not a bound independent of `n`. Use
   Caccioppoli with a middle cutoff equal to one near the inner cutoff support
   to control the weighted first-jet energy appearing in the inner
   commutator. Bounds on the cutoff values, first derivatives, second
   derivatives, and `|y|` must depend only on the fixed geometry and `c`.
   Existence of a plateau alone does not furnish a stated numerical bound
   such as `0≤η≤1`; either prove it for the construction or retain an actual
   finite bound on `|η|`. The new pointwise/support norm drafts expose the
   correct actual coefficient sums, but require the remaining integral and
   local-energy composition.

4. **Positivity and selected derivative bounds.** The exact energy identity
   and preliminary elliptic step allow every real `c`. Coercive use requires
   `c≥0`; the unweighted spectator derivative bound
   `16c Σ_j‖D_tj u‖²≤‖P_cu‖²` requires `c>0` to give finite control when
   spectator directions are present. At `c=0`, a product of a smooth compact
   `y` function and a discontinuous L² `t` function has L² `P_0` output but
   need not have an L² spectator derivative. This is a scope obstruction, not
   a defect in the existing `c=0` inequalities.

5. **Anisotropic limit and eventual indices.** One gain controls `D_y`,
   `D_t`, and the ordered `D_yD_y` derivatives. It does not control all
   unweighted spectator second derivatives or all mixed derivatives. The
   existing full-H² bounded-limit wrapper therefore cannot be applied to the
   entire `4+m` first-direction family. The new anisotropic limit core uses
   precisely the permitted selected operators and avoids that mistake.
   Product transport and the actual uniform bound must be supplied. Reindex
   past the common eventual threshold, or prove an eventual-bound version,
   before invoking a limit theorem whose bounds and weak-jet identities are
   quantified over every natural index. Strong convergence of a fixed cutoff
   times `G_n` also needs its bounded L² multiplication map.

6. **Dimension and physical interpretation.** The preliminary theorem permits
   an arbitrary finite real inner-product spectator space with a chosen
   orthonormal basis; the sealed energy/commutator API is explicitly
   `R⁴ × EuclideanSpace ℝ κ`. Instantiate that representation or provide the
   exact isometric transport before claiming arbitrary spectator-space scope.
   The `y` Hessian sum has 16 ordered entries, including both orders of mixed
   derivatives; it is not the ten-component unordered sum. The operator
   constants `16c` and `3/2` do not introduce a spectator-count factor, but
   chosen cutoff derivative bounds may depend on that dimension. Current
   sources are complex scalar statements. Finite spin-component summation
   and a common choice of geometric constants/threshold remain explicit
   composition steps before a full spin-space statement is claimed.

A sound order of composition is therefore: local input extension when
needed; fixed interior geometry; the uniform eventual partial-regularization
equation and preliminary local H²; an outer global plateau cutoff; local
Caccioppoli for a middle cutoff; the inner commutator's uniform L² output
bound; compact weak Grushin estimates; selected derivative limits after
reindexing. Principal-output identification must occur on the region where
the equation holds before replacing it by the forcing in any bound.

This route establishes an anisotropic local gain if those obligations are
discharged. It does not establish joint local H² of the original solution in
one step, analyticity, the factorial recurrence, certified computation, or
full Theorem T. The review found no justification for any of those stronger
claims in these three checkpoints.

Development object caches were reused in the cited audits; these sources are
outside the sealed 671-target desktop rebuild. Frozen preservation anchor:
`rwa_proof/RWA_THEOREM.md`, SHA-256
`d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`,
commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`.
