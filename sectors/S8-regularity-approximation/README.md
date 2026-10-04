# S8: Regularity of eigenfunctions and approximation rates

**Scope.** The structure of eigenfunctions at particle coalescences (cusps, logarithms, analyticity), and rigorous approximation rates for explicit bases with explicit constants.

## Current best (v1.0 foundation)

| Claim | Result | Tier |
|---|---|---|
| S8-001 | Weighted all-order (analytic-type) bounds for the helium ground state's extracted remainder, uniformly up to the triple-collision vertex | P1, **needs expert review** |
| S8-002 | $`H^2`$ approximation rate $`C e^{-c n^{1/3}}`$ for helium by an explicit dyadic-exponent dictionary (existence only) | P1, **needs expert review** |
| S8-003 | "Theorem C": in any fixed-exponent Hylleraas family, the residual is $`\ge c(n+1)^{-72}`$ | P1 |

**Why S8-001 matters.** If it is correct, it goes beyond the published regularity at the triple point: $`C^{1,1}`$ factorization (Fournais–Hoffmann-Ostenhof–Hoffmann-Ostenhof–Østergaard Sørensen 2005), and analyticity at isolated pair collisions (same authors, 2009). It is also the analytic foundation of the Theorem T program (S2). So far only AI agents have reviewed it.

**Formal progress.** `lean/Foundation/` also contains Lean modules on the physical ground state's regularity and decay: rotation invariance, boundedness, the exponential $`H^2`$ tail, and the Kato–Stummel/Grušin machinery. Those modules have no statement cards yet. Writing cards for them is open problem S8.5.

## Open problems

| ID | Problem | Deliverable | Status |
|---|---|---|---|
| S8.1 | **Human referee report on S8-001** | A review record (see `reviews/TEMPLATE.md`) of [`rwa_proof/RWA_THEOREM.md`](../../archive/v1.0-research-notes/rwa_proof/RWA_THEOREM.md), [`UNIFORM_ANALYTIC_AUDIT.md`](../../archive/v1.0-research-notes/rwa_proof/UNIFORM_ANALYTIC_AUDIT.md) and the Kato–Stummel descent notes in [`continuation/audits/`](../../archive/v1.0-research-notes/continuation/audits/). It should confirm the result or exhibit a gap. | open |
| S8.2 | **Human referee report on S8-003** | A review, or a sharper exponent than 72 | open |
| S8.3 | **Explicit constants for S8-002** | Numerical $`C, c`$, or a lower bound refuting the rate | open |
| S8.4 | **Check a claimed misprint** | The notes ([`ISSUE_KS_SOURCE_DEGREE_v2.md`](../../archive/v1.0-research-notes/continuation/audits/ISSUE_KS_SOURCE_DEGREE_v2.md)) claim that one coefficient bound in arXiv:0806.1004v1 (eq. 4.41) is false as literally stated, and that the headline theorem is unaffected. Check it against the published journal version *before* anyone asserts it publicly, and contact the authors if it holds up. | open |
| S8.5 | **Statement cards for the regularity modules** | Cards for the decay and regularity Lean modules, with a definitions audit | open |

## Submitted continuation: homogeneous Grushin initialization

[S8-004](../../claims/cards/S8-004.md) submits a kernel-checked one-step estimate
for the existing homogeneous weak Grushin equation. A supplied continuous
potential bound $`|B| \le b`$ on a compact region converts the potential-weighted
input norm to an ordinary local $`L^2`$ norm. The compact region and base constant
are fixed before the potential, its bound and the solution. The output gives
actual first Y/T and ordered second YY weak derivatives of the cutoff, with
explicit factors in $`b`$ and no input derivative premise.

This is submitted evidence pending human maintainer statement review. Full joint
$`H^2`$, $`H^{12}`$, all-order factorial bounds, and physical Coulomb-chart
coefficient estimates remain separate tasks. This prerequisite does not close
all of Rung 2 or Theorem T. The new source is
[`ManyBody/S8/HomogeneousGrushinOneStep.lean`](../../lean/ManyBody/S8/HomogeneousGrushinOneStep.lean).

## Submitted continuation: actual nuclear-chart initialization

[S8-005](../../claims/cards/S8-005.md) derives the bounded-potential input from
actual two-electron Coulomb geometry and the physical Hamiltonian graph. On
positive-radius nuclear KS charts with radius at most one, the coefficient is
bounded by $`26|Z|/3+8/11+|E|/2`$. The selected nuclear collision belongs to the
chart, and smooth compact plateau cutoffs exist around it. The output gives
first Y/T and ordered YY weak derivatives of a physical representative with
explicit local norm factors. The base compact set and constant precede the
charge, energy and eigenfunction. Their dependence on chart scale remains;
the uniform statement concerns the coefficient bound only.

This topic-branch result is pending human maintainer review. The accepted
current-best table is unchanged. H12, factorial estimates, and all of Rung 2
remain open.

## Submitted continuation: genuine joint nuclear KS H2

[S8-006](../../claims/cards/S8-006.md) derives genuine local weak $`H^2`$ for
physical KS pullbacks on every existing nuclear coefficient patch, for every
electron count. One spin representative works before all components, charts
and cutoffs. The proof constructs actual TT diagonal derivatives from the
spectator differentiated equation and combines them with YY derivatives through
the exact frozen product Fourier theorem, giving all ordered mixed derivatives.
The selected nuclear collision is included whenever the other singularities are
separated. A two-electron specialization also proves the first spectator
forcing budget using $`|D_T B|\le8|Z|/9+128/121`$.

This submitted evidence is pending human maintainer statement review. It proves
qualitative joint H2, while H12 initialization, uniform finite-order budgets,
all-order factorial estimates and Rung 2 remain open.


## Submitted continuation: original-state budgets and actual rescaling

[S8-007](../../claims/cards/S8-007.md) closes the local norm inputs in the
first spectator bootstrap by explicit original spin-state budgets. It also
proves the actual anisotropically rescaled physical weak equation, including
integrability and the necessary coefficient $`r B(Z,rE)`$. On one fixed
unit-chart cutoff, the compact set and gain constant precede every positive
radius, charge, energy and state; the rescaled first Y/T and YY squared norm
bounds use $`b=r(26|Z|/3+8/11+r|E|/2)`$ and the original Moser amplitude.
These geometric witnesses are radius-independent for that fixed rescaled
cutoff. They do not supply full joint H2 budgets or a shrinking-cutoff family.
H12 and factorial estimates remain open; human statement review is pending.


## Submitted continuation: actual isolated-pair KS H2

[S8-008](../../claims/cards/S8-008.md) proves genuine local joint weak H2
for the original two-electron physical eigenfunction on its actual pair KS
patch, including the selected pair collision and excluding nuclear collisions.
The orthogonal Hadamard reconstruction derives both original positions,
principal c=4 and cleared repulsion constant 8/sqrt(2). The actual equation,
its integrability and removability are proved. Every isolated physical pair
collision away from the nucleus is represented by a transverse-zero chart
point. This qualitative result is pending human review and does not supply
H12, simultaneous-collision coverage or factorial estimates.


## Submitted continuation: full joint nuclear KS H3

[S8-009](../../claims/cards/S8-009.md) proves all ordered third weak L2
derivatives of every smooth compact cutoff of the physical nuclear KS
pullback, for every electron number and selected index. The same cutoff output
has genuine arbitrary-direction first, second and third derivative families.
The actual Y commutator and spectator recurrences supply the new derivatives;
the physical theorem assumes only the original graph and representative.
The selected nuclear collision is included on the existing patch. Human review
is pending; this qualitative result does not supply H12 or factorial budgets.


## Submitted continuation: second spectator original-state budgets

[S8-010](../../claims/cards/S8-010.md) derives the next finite spectator
stage from the original physical graph. Two nested plateaus supply actual
second spectator derivatives; their inner Y/T/YY squared norm sums obey one
explicit original spin-state norm bound. A proved mixed second coefficient
bound is 128|Z|/27+8192/1331. The cutoffs and geometric constant precede
charge, energy and state. Human review is pending. This finite fixed-chart
budget does not provide full H12 or factorial estimates.


## Recovered later checkpoint and new norm uniformity

The [latest recovery checkpoint](../../recovery/rung2-latest-2026-10-04/CURRENT_CHECKPOINT_v1.md)
restores the original local H12, factorial, pointwise and analytic-descent chain,
its actual mixed derivative estimates and within-chart compatibility, plus
scalar-ground decay and axis/distance components. The finite-stage submissions
above describe their own narrower conclusions. Recovery does not promote an
accepted claim or establish the remaining global approximation and solver steps.

[S8-014](../../claims/cards/S8-014.md) supplies a common local Lipschitz coefficient
before every physical eigenstate at fixed electron count, charge, energy and
configuration-ball radius. The actual graph constructs a shared full-spin
representative, with component Lipschitz constants bounded by that coefficient
times the original spin-state norm. The coefficient follows from uniform
boundedness on the closed physical eigenspace; it is existential and has no
numerical algorithm. The fixed radius 1 is available before the state. Human
statement review is pending, and the full rung remains open.


## Submitted continuation: one finite collision-chart family at all radii

[S8-016](../../claims/cards/S8-016.md) proves a finite physical unit-center
family before every radius, covering the entire punctured two-electron
configuration space by scaled collision-free, nuclear and pair neighborhoods.
The original half-sum pair center and its inverse-square-root-of-two normalization
are explicit. At relative widths at most 1/16, each selected-collision
neighborhood excludes the remaining physical singularities. This is a geometric
cover: the triple origin and analytic applicability remain separate obligations.
The finite centers are existential; human statement review remains pending.


## Submitted recovered-source consumers: fixed geometry and original physical norms

[S8-011](../../claims/cards/S8-011.md) extends the actual physical ground
pointwise/analytic endpoint to the exact-product threshold and Z=3/2.
[S8-015](../../claims/cards/S8-015.md) chooses common constants before every
physical spin eigenstate, fixes ballradius1 and all scales through1/4, and
bounds the genuine physical factorial/pointwise amplitudes by the original
state norm. [S8-012](../../claims/cards/S8-012.md) adds actual complex/real
mixed derivative data with the recovered factor24; its normalized lower-charge
ground endpoint has the common base budgets. [S8-013](../../claims/cards/S8-013.md)
returns literal analytic-plus-distance germs to the original unscaled physical
function and proves separate real germ/jet compatibility across admissible
scales and centers in one fixed physical collision coordinate map.

These consumers depend on the sealed recovered proof archive and preserve its
source bytes, original c=1 pair convention and exact domains. The common norm
constants are non-effective. Full committed verification and human acceptance
remain separate from focused kernel checks. Ambient distance germs, complete
collision/exterior applicability, global approximation and solver obligations
remain open.


[S8-017](../../claims/cards/S8-017.md) additionally chooses a common positive
width and finite physical centers before every state and proves actual analytic
applicability on all selected nuclear/pair neighborhoods for radii through1/4.
It reconstructs the original physical representative at every neighborhood
point; the restored pair uses scale rho/sqrt(2). The covered collision-free bulk,
triple origin and exterior still need separate analytic estimates.


## Submitted continuation: actual ambient nuclear distance reconstruction

[S8-018](../../claims/cards/S8-018.md) reconstructs the actual normalized
scalar Coulomb ground function at charge at least2 on a full complex polydisc
in the three physical distances near each selected nuclear collision. The
literal bounded SO(2) descent is composed with rational axis coordinates and
exactly returned to the original state. A proved O(3) orbit bridge includes
collinear and zero selected positions. Both nuclear indices and every
admissible positive scale of the same representative are retained. This
uses the recovered selected-state L,R and u0 budgets; quantitative norm
uniformity is a separate result. Human statement review and full committed
verification are pending. Pair/triple collision reconstruction, ambient germ
compatibility and the full rung remain open.


## Submitted continuation: actual ambient pair distance reconstruction

[S8-019](../../claims/cards/S8-019.md) proves bounded holomorphic A/B
functions of three independent complex distances near an isolated pair
collision, from the same actual normalized scalar ground witness at Z>=2.
The principal complex square-root branch and its full-polydisc domain, actual
canonical configuration distances and degenerate-safe physical orbit identity
are derived. The new functions reconstruct the actual normalized origin
difference at every admissible scale; original unscaled coefficients are a
separate extension. Both nuclear collisions and the triple origin are
excluded. Human statement review and full committed verification are pending.
