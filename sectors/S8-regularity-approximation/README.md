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
uniformity is a separate result. Original committed full verification passed
at head3f71054c7be8 (see the card); recovery acceptance, resulting integration
verification and human statement review remain pending. Pair/triple collision reconstruction, ambient germ
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
excluded. Original committed full verification passed at head3f71054c7be8
(see the card); recovery acceptance, resulting integration verification and
human statement review remain pending.


## Submitted continuation: original annular mixed derivative budgets

[S8-020](../../claims/cards/S8-020.md) gives genuine Euclidean physical
coordinate mixed derivative budgets for the literal original A/B functions
on every selected finite nuclear/pair annular neighborhood. A positive
quarter-polydisc shrink and finite centers precede the state. The exact
positive scale gives epsilon^(1-n) for positive-order A and epsilon^(-n)
for B, with A's original Moser value at order zero. The common amplitudes
are proportional to the original full-spin norm. Collision-free bulk,
triple origin and all-direction operator norm bounds remain separate.
Human review and full committed verification are pending.


## Submitted continuation: genuine global H2 component moments

[S8-022](../../claims/cards/S8-022.md) constructs genuine polynomial
configuration-radius L2 moments of the actual normalized scalar ground state
and every ordered first/second weak derivative at Z>=2. For each positive
a with a^2<Z^2/112, one actual exponentially weighted component norm
precedes all orders k and bounds the combined moments by C*k!/a^k.
These outputs weight the original derivative components; weak derivatives
of the weighted state and exact rational dictionary overlaps are separate.
Human review and full committed verification remain pending.


## Submitted continuation: original distance reconstructions and overlap

[S8-021](../../claims/cards/S8-021.md) proves equality throughout the full
common complex domain of two nuclear distance reconstructions for the same
actual original ground function, with complex germs and every ordered jet.
A real feasible triangle ball derives the initial equality from physical
reconstruction; analytic continuation supplies the nonreal domain.
[S8-023](../../claims/cards/S8-023.md) returns the literal pair ambient A/B
functions to the original ground representative, preserving the correct
epsilon on A and no extra epsilon on B. Both use Z>=2 and the selected
state's original positive scale range. Separate coefficient compatibility,
collision-type transitions, triple origin and a global atlas remain open.
Human statement review and full committed verification remain pending.


## Submitted continuation: compact physical H2 truncation

[S8-024](../../claims/cards/S8-024.md) constructs literal compact truncations
of the actual scalar ground graph at Z>=2. Genuine first and all ordered
second product-rule weak derivatives have combined H2 defect at most
C*exp(-a*R), for a^2<Z^2/112, with C before every R>=1. Compact support
applies to the displayed AE representative, and the cutoff state need not
be smooth or an eigenfunction. Finite dictionary approximation, computable
prefactors and the complete rung remain open. Human statement review and
full committed verification are pending.


## Submitted continuation: actual pair ambient distance derivatives

[S8-025](../../claims/cards/S8-025.md) derives all-order factorial operator
norms and literal ordered distance-word bounds from the actual bounded
holomorphic pair A/B/H profiles at Z>=2. The half-polydisc radius and exact
original epsilon powers are explicit; only order zero retains u0. The
complex Fin3 Pi norm and selected-state L,R budgets are retained. Human
statement review and full committed verification remain pending.


## Submitted continuation: true physical annular operator norms

[S8-027](../../claims/cards/S8-027.md) strengthens the actual full-spin
coordinate estimates to genuine real Frechet operator norms on the literal
Position-times-Position product norm. Taylor support and coefficients derive
the directional estimates, and physical lifts derive balance. Constants and
finite quarter-width centers precede the state. Original epsilon factors,
norm-linear amplitudes and actual reconstruction are retained. Human
statement review and full committed verification remain pending.


## Submitted continuation: identify actual separate complex collision profiles across scales

[S8-026](../../claims/cards/S8-026.md) proves that for charge at least2, the same actual normalized scalar Coulomb ground representative has equal literal original A,B and H profiles throughout the common complex nuclear or pair distance polydisc at any two admissible scales sharing a positive collision-distance point. Real feasible triangle balls and actual reconstruction derive H equality. Genuine selected-distance parity separates A and B, including the collision face by holomorphic continuation. Every complex overlap germ and ordered Frechet jet agrees.
The nuclear comparisons fix one selected index. Collision-type transitions, triple origin and the global atlas remain open. No profile parity or equality is supplied to the physical graph consumer; all original state facts are retained.
Human statement review and full committed verification remain pending.


## Submitted continuation: bound actual compact physical hamiltonian residuals exponentially

[S8-028](../../claims/cards/S8-028.md) proves that for charge at least2, the same actual normalized scalar ground state and ordered weak derivative families have compact cutoff H2 approximants with a true scalar Coulomb graph output and eigenvalue residual at the original ground energy bounded by C*exp(-a*R). Each positive a with a^2<Z^2/112 has one finite C before every real R at least1. Full literal compact AE support, product-rule weak derivatives and the genuine H2 defect bound are retained. Graph output existence is derived from the actual H2 domain.
The compact state need not be normalized, smooth or an eigenfunction. The prefactor is existential and selected-state dependent. Computable radii, finite dictionaries, rational matrices, effective solver and the full rung remain open.
Human statement review and full committed verification remain pending.


## Submitted continuation: bound actual nuclear ambient distance derivatives at all orders

[S8-029](../../claims/cards/S8-029.md) proves that for charge at least2, the same actual normalized scalar ground witness has genuine all-order complex Frechet operator norms and ordered distance coordinate-word factorial budgets for literal original nuclear A,B and H, for both selected indices at all admissible scales and every half-polydisc point. Actual bounded holomorphic profiles discharge derivative estimates. A,H carry epsilon times epsilon^(-n) and u0 only at order zero, while B carries epsilon^(-n). All original physical and spectral facts are retained.
The norm is the actual complex Fin3 Pi norm. Selected-state L,R and amplitude are retained. No norm-uniform all-state upgrade, real-distance transport, global approximation, computable prefactor or full rung is claimed.
Human statement review and full committed verification remain pending.


## Submitted continuation: identify actual complex nuclear profiles across indices and scales

[S8-031](../../claims/cards/S8-031.md) proves that for charge at least2, the same actual normalized scalar ground witness has equal original nuclear A,B and H functions throughout the common full complex distance domains at arbitrary nuclear indices and admissible scales sharing a positive collision-distance point. The literal exchanged physical configuration and actual ground exchange law derive real values, then analytic continuation and genuine profile parity derive whole-domain separate coefficient equality, every complex germ and all ordered jets.
Local q records selected nuclear radius, spectator radius and pair distance. Equality is not an input premise. Original selected-state scales and physical facts are retained. Collision-type transitions, triple origin, a global atlas, dictionary approximation and the full rung remain open.
Human statement review and full committed verification remain pending.


## Submitted continuation: normalize compact physical h2 approximants with true rayleigh error

[S8-030](../../claims/cards/S8-030.md) For charge at least2, the same actual normalized scalar ground state and its genuine first and ordered second weak derivatives admit literal norm-one compact H2 approximants. Each a>0 with a^2<Z^2/112 has one finite C before every R at least max1(2C/a). The raw cutoff norm is at least1/2. Full actual H2 defect, true scalar Coulomb graph eigenvalue residual and absolute actual Rayleigh pairing error are all bounded by C*exp(-a*R), with literal compact AE support and genuine weak derivative and defect families.
The threshold is explicit in the existential selected-state/rate constant, which is not computably extracted. The original ground retains realness, exchange and O3 symmetry; those symmetries of the normalized cutoff are not asserted. Smoothness, finite dictionaries, effective solver and full rung remain open.
Human statement review and full committed verification remain pending.


## Submitted continuation: bound genuine real distance derivatives of original collision profiles

[S8-032](../../claims/cards/S8-032.md) For charge at least2, the same actual normalized scalar ground witness and original nuclear and pair A,B,H profiles have genuine all-order real Frechet operator and ordered distance-coordinate-word factorial budgets. The literal complex profiles are composed with the actual coordinatewise real cast. A proved norm-preserving cast and exact iterated derivative restriction transport the actual complex estimates, with the exact original epsilon powers and u0 term only at order zero. All physical ground facts are retained.
The real domain is the actual Fin3 Pi maximum norm with complex values. This is a derivative bound in independent ambient distance coordinates; physical Cartesian transport or profile realness is not asserted. Selected original scales/amplitudes remain. Global approximation and full rung remain open.
Human statement review and full committed verification remain pending.

## Submitted continuation: derive actual distance taylor sums and geometric truncation errors

[S8-033](../../claims/cards/S8-033.md) Actual complex distance profiles of the same normalized physical ground have canonical derivative-coefficient Taylor sums, explicit geometric value remainder, and genuine operator-norm Taylor remainders for every derivative field on the stated quarter polydiscs. All nuclear indices and admissible scales are retained.
The derivative-field polynomials are stated separately; no coupling as derivatives of one value polynomial, effective coefficients, global atlas or full rung is claimed.
Independent AI applicability review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: construct smooth normalized compact physical ground approximants

[S8-035](../../claims/cards/S8-035.md) The same actual normalized two-electron ground and genuine weak first and ordered second derivatives admit concrete smooth normalized compact approximants at every positive tolerance, with simultaneous physical H2 defect, actual Coulomb graph residual and absolute Rayleigh pairing error bounded by that tolerance. A single eventual concrete mollifier index controls all 43 components.
The selected-state constants and eventual mollifier index are existential. The radius formula is explicit in those constants. Symmetry of the new approximants, finite dictionaries, computable coefficients, effective solver and full rung are not asserted.
Independent AI applicability review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: preserve actual ground symmetries under radial physical compact truncation

[S8-034](../../claims/cards/S8-034.md) For charge at least2, one actual normalized scalar Coulomb ground with original weak derivative families admits literal norm-radial compact truncations preserving actual exchange, reality and simultaneous O3 invariance. Each positive admissible decay rate has one constant before all real radii at least1, controlling both the true combined H2 defect and actual scalar Hamiltonian graph residual at the original ground energy.
The new cutoff is the explicit inner-product-space radial bump, not an inferred symmetry of the old generic choice. Compact states are not asserted normalized, smooth or eigenfunctions. Constants are existential; finite dictionaries, effective solver and full rung remain open.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: derive actual ambient profile reality and canonical real taylor coefficients

[S8-036](../../claims/cards/S8-036.md) The same actual normalized physical ground and nuclear and pair collision profiles are real throughout the full real distance slices. Genuine feasible physical triangle values, real analytic continuation and actual parity derive separate A,B,H reality including the collision axis. Every ordered real derivative jet has zero imaginary part, and the unchanged canonical complex Taylor coefficients and finite value polynomials are real on actual real increments. All original ground and derivative-budget facts and the actual Taylor sums and errors are retained.
Only real arguments and directions are asserted real. No arbitrary complex-direction or nonsymmetric power-series coefficient reality is claimed. Selected original scales remain; coupled polynomial derivative errors, rational coefficients, global approximation and full rung are separate obligations.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: couple actual distance taylor polynomial gradient and hessian errors

[S8-037](../../claims/cards/S8-037.md) For the same actual normalized physical ground and original nuclear and pair A,B,H profiles, every literal finite canonical Taylor polynomial has genuine iterated derivative equal to the correctly shifted Taylor truncation of the corresponding actual derivative field. On the actual quarter polydiscs this gives simultaneous geometric value, gradient and Hessian errors for that one polynomial in true multilinear operator norms, while retaining all original physical and spectral facts.
Errors are in independent complex ambient distance coordinates. Physical Cartesian pullback H2 integration, rational or effective coefficient choice, global approximation and full rung are separate obligations.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: normalize radial compact physical approximants while preserving ground symmetries

[S8-038](../../claims/cards/S8-038.md) The same actual normalized scalar Coulomb ground and original genuine weak derivative families admit norm-one radial compact H2 approximants preserving actual exchange, reality and simultaneous full O3 invariance. For each positive admissible decay rate one nonnegative constant precedes every real radius beyond the explicit normalization threshold and controls the true combined H2 defect, actual scalar Hamiltonian graph residual and absolute Rayleigh pairing error exponentially.
The radius threshold is explicit in the existential selected-state/rate constant. Smoothness, finite dictionaries, computable constants or coefficient selection, solver termination and full rung remain open.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: approximate actual physical collision profiles by rational distance polynomials

[S8-039](../../claims/cards/S8-039.md) The same actual normalized physical ground and its original nuclear and pair A,B,H admit literal finite unshifted distance monomial polynomials with rational coefficients. Each prescribed positive tolerance selects one polynomial per profile controlling its true real value, gradient and Hessian uniformly on the fixed closed inner distance box. Actual finite Taylor representation, rational density and coupled derivative errors are derived; all original physical and spectral facts are retained.
Selection is existential and no effective coefficient or order algorithm is claimed. These errors are in independent real distance coordinates; physical H2 pullback, global finite dictionaries, solver and full rung remain separate.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: prove smooth compact density in the actual scalar coulomb graph

[S8-040](../../claims/cards/S8-040.md) For every real charge and arbitrary actual scalar Coulomb graph pair f,h, genuine original weak derivative families are selected before every positive tolerance. A smooth compact physical representative supplies one approximating state with genuine weak and classical first and all ordered second derivative families, combined43component H2 defect and actual graph output difference each bounded by that tolerance. True L2 exterior convergence, finite component truncation, smoothing and actual graph output existence are proved without a ground, eigenvalue or weighted decay input.
This is actual metric graph approximation; no separately defined abstract operator core predicate is asserted. Radius and mollifier index are existential. Approximants are not asserted normalized, real or symmetric for arbitrary states. Effective rate, finite dictionary, solver and full rung remain open.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: construct genuine radial smoothing and normalized symmetric smooth ground approximants

[S8-042](../../claims/cards/S8-042.md) The same actual normalized scalar Coulomb ground and original weak derivatives admit norm-one smooth compact approximants preserving actual exchange, reality and simultaneous O3 invariance both as physical L2 classes and at every point of the literal smooth representatives. One constant before every positive tolerance supplies the cutoff radius, and every sufficiently late index of a literal normalized radial kernel controls the true43component H2 defect, actual scalar graph residual and absolute Rayleigh pairing error by the tolerance. Actual kernel mass, convergence, covariance and weak and classical convolution derivatives are derived.
The kernel is the literal radial cutoff divided by its actual positive integral. No symmetry of a classically chosen old mollifier is inferred. Constants and sufficiently late index are existential; no finite dictionary, effective coefficient selection, solver termination or full rung is claimed.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: approximate every normalized symmetric scalar graph state by genuine smooth compact states

[S8-044](../../claims/cards/S8-044.md) Every actual normalized scalar Coulomb graph pair at any real charge, with explicit original exchange, reality and simultaneous O3 symmetry, admits norm-one smooth compact approximants preserving these symmetries both in the actual physical L2 class and pointwise on the literal smooth representative. Genuine original first and ordered second weak derivatives precede every tolerance; one cutoff radius and every sufficiently late actual radial-kernel index control the true43component H2 defect, actual graph difference and absolute Rayleigh pairing difference by that tolerance.
No eigenvalue, charge lower bound, spectral gap, decay or approximation premise is used. Radius and sufficiently late index are existential; no symmetry of the graph image, rational dictionary, effective selection, solver termination or full rung is claimed.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: preserve actual coulomb graph image symmetries in normalized smooth approximation

[S8-046](../../claims/cards/S8-046.md) Actual scalar Coulomb graph covariance and output uniqueness transport every original permutation, reality and simultaneous orthogonal symmetry to the original graph output. For every real charge, the same actual normalized symmetric smooth compact two-electron approximants have actual graph outputs with exchange, AE reality and fullO3 symmetry, retaining the true43component H2, originalstate, graph difference and absolute Rayleigh difference bounds at every positive tolerance.
Output symmetry is derived from the actual input and graph, with no eigenvalue, gap, decay, outputsymmetry or approximationexistence premise. No smooth compact representative of the graph output, rational dictionary, effective selection, solver or full rung is asserted.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: bound actual collision taylor orders linearly in requested dyadic precision

[S8-045](../../claims/cards/S8-045.md) The same actual physical Coulomb ground witness admits one common linear dyadic Taylor order N=2p+m+2 at each original nuclear and pair collision distance chart. A fixed natural offset before every precision controls the actual real zero, first and second derivative operatornorm errors for A, B and H by onehalf to the powerp, uniformly on the true open quarter distance box. Every retained graph, spectral, H2, decay, symmetry, reconstruction and rational approximation fact belongs to that same original witness.
The offset can depend on state, scale and chart and is existential; no uniform acrossscales offset or algorithm for physical budgets and coefficient extraction is proved. Taylor coefficients are not asserted rational. This gives local linear ordergrowth with no rounding bitcost, composed physical H2 error, global atlas, triplecollision, solver or full rung conclusion.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: preserve actual collision parity and reconstruction in rational distance approximants

[S8-043](../../claims/cards/S8-043.md) The same actual normalized Coulomb ground admits finite rational A and B distance polynomials globally even in the selected nuclear or pair distance. Their one reconstructed polynomial PH=PA+qjPB, with a proved finite rational monomial dictionary, approximates the actual original H while PA and PB approximate the actual A and B in true real value, gradient and Hessian operatornorms uniformly on the closed inner distance box. Original profile analyticity, parity and reconstruction are derived from that same graph witness.
The exact selected coordinate is zero for nuclear and two for pair charts and the original inner radius is epsilon delta over8. Polynomial selection is existential. No composed physical H2 error, degree or cardinality rate, computable coefficient choice, global dictionary, solver or full rung is asserted.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: bound actual dyadic collision distance dictionaries by a cubic monomial count

[S8-048](../../claims/cards/S8-048.md) The literal canonical real Taylor dictionary for the same actual nuclear and pair collision A, B and H profiles has total degree below N and at most N cubed monomials at the common linear order N=2p+m+2. Actual support and coefficient definitions give exact global equality with each genuine value polynomial and its actual derivatives, retaining simultaneous true real value, gradient and Hessian errors at most onehalf to the powerp on the quarter distance box.
The actual translated multilinear expansion derives the finite dictionary and the orderzero support is proved empty. Original real Taylor coefficients are not asserted rational or effectively extractable; no coefficient bitcost, physical H2 composition, global dictionary, solver or full rung is proved.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.

## Submitted continuation: choose linear physical cutoff radii for dyadic normalized coulomb approximation errors

[S8-049](../../claims/cards/S8-049.md) Every actual normalized symmetric Coulomb ground has an explicit physical radial cutoff radius linear in requested dyadic precision, max original normalization threshold and log oneplusC overa, plus p logtwo overa. The same actual normalized radial compact state has state L2 and true43component H2 defects, actual scalar eigenvalue residual and absolute Rayleigh error at most onehalf to the powerp, preserving exchange, AE reality and fullO3 state symmetry. Genuine original derivative families precede the rate and every precision.
Actual ground decay and approximation bounds are derived, with no exponential approximation premise. The prefactor remains existential and no algorithm finds or evaluates the original state. This cutoff is not asserted smooth, a finite dictionary or computable representation; no coefficient bitcost, solver or full rung follows.
Independent AI source/card/artifact review passed; human statement review and exact committed full verification remain pending.
