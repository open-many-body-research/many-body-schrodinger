> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Exact hydrogen computation and conditional spectral certification

This checkpoint records new results beyond the all-electron operator and spectral foundation. The complete two-electron Theorem T remains unverified. The physical Hamiltonian, simultaneous spatial/spin antisymmetry and actual weak H² domain are unchanged.

## Exact one-electron result

For every real Z>0, the actual full-spin one-electron Coulomb operator has graph, H¹-form and spectral ground energy −Z²/2. Its domain contains two independent ground eigenvectors, obtained by placing the actual exponential exp(−Z|x|) in the two spin components. The radial function, its singular second derivatives and the graph eigen equation are proved, using regularization and weak derivative limits. This is not an assumed eigenpair. An upper bound of two on ground multiplicity is not part of this checkpoint.

For natural Z and requested precision p, including Z=0, the Lean definition hydrogenExactSolver returns the rational pair (−Z²/2,−Z²/2). The exact checker accepts precisely these endpoints. Its soundness theorem bounds the actual continuum spectral infimum and proves zero width, hence width at most 2^−p. Both definitions are computable. The theorem uses standard foundational axioms; sample outputs are checked by kernel reduction. Runtime evaluator and CLI outputs are diagnostic executions, not additional proof foundations. No dependence on an impractical bounded-box schedule is needed for this subcase.

Sources: lean/HydrogenSpinGround_v1.lean and lean/HydrogenExactSolver_v1.lean. Strict expanded statement/axiom audit: audits/formal_semantics/20260910T014448_818697Z/receipt.json, 21 declarations. Independent semantic review: audits/HYDROGEN_SPIN_SOLVER_ROOT_REVIEW_v1.json. The exact hydrogen complement −Z²/8 still requires new formalization; its reviewed paper proof is recorded separately.

## A spectral enclosure with explicit physical comparison inputs

Let H be the actual N-electron fermionic operator, let l be a bounded complex scalar functional on its Hilbert space, and suppose C>=0 and

    beta ||x||² <= Re<x,Hx> + C |l(x)|²       for every x in D(H).

Let psi be an actual unit domain vector, let mu=Re<psi,Hpsi>, and suppose

    L <= mu <= U < beta,       ||Hpsi-mu psi||² <= r.

Then the actual continuum spectral infimum lies in

    [L-r/(beta-U), U].

The theorem first derives that the ground energy is below beta. At a real spectral point, failure of an approximate unit vector would give an actual bounded two-sided inverse, contradicting spectral membership. The finite scalar defect makes a suitable approximate sequence converge in norm; closedness puts its nonzero limit in the actual domain. Thus the bottom is an eigenvalue. A rank-one cancellation argument supplies the full orthogonal-complement form bound, and symmetric-operator eigenvector orthogonality excludes any other spectrum below beta. Finally an unbounded-domain Temple inequality gives the interval. The proof needs neither D(H²) nor a finite-dimensional expansion.

This is a conditional formal theorem. Its actual global comparison, unit trial, mean bounds and residual bound must be established for any concrete certificate. No hydrogenic comparison, exact physical moment formula or executable two-electron certificate producer is supplied by simply quantifying these premises. Ground attainment and a gap, however, are derived rather than assumed. The ionization threshold is never silently used as a discrete-state separator.

Sources: lean/CoulombRankOneBranch_v1.lean and lean/CoulombRankOneCertificate_v1.lean, supported by the actual approximate-eigenvector and scalar-defect chain and HardyTemple modules. Strict audit: audits/formal_semantics/20260910T013841_799876Z/receipt.json, 12 declarations, complete axiom reports and no statement ellipses. Only propext, Classical.choice and Quot.sound occur. Noncomputable selection in the attainment proof is an existence argument, not an algorithm for finding the eigenvector.

## A version permitting degeneracy

Replacing l by a bounded map into C^m gives actual eigenvalue attainment at every real spectral point below beta. Every linear subspace of the actual operator domain whose Rayleigh form is bounded above by a fixed r<beta has dimension at most m: the comparison map is injective on that subspace. In particular each actual eigenspace below beta is finite-dimensional with dimension at most m.

For the physical Coulomb operator, one actual unit trial below beta consequently gives ground attainment and this bound on ground multiplicity. It does not give the rank-one beta-complement bound when m>1, nor a distinguished ground vector. This is the appropriate explicit distinction for possible degenerate many-electron applications. No physical finite-rank comparison has yet been instantiated for lithium here.

Sources: lean/FiniteDefectCauchy_v1.lean, FiniteDefectKernel_v1.lean, FiniteDefectSpectralAttainment_v1.lean, FiniteDefectDimension_v1.lean and CoulombFiniteDefectGround_v1.lean. Strict audit audits/formal_semantics/20260910T014923_918031Z/receipt.json passes all seven declarations with complete standard-only axiom reports and no ellipses. These sources completed after the 192-target source capsule and are excluded from its exact scope.

## A formal helper for the next physical gap proof

PartnerGapTransfer_v1 works on a complete domain space D and a Hilbert space E with continuous maps J,A,B from D to E. Assume a positive bound ||v||_D<=K||Bv||, a value bound c||Jv||<=||Bv||, the actual integration pairing <Au,Jv>=<Ju,Bv>, and (ran B)^orthogonal=span{g}. It derives c||Ju||<=||Au|| for <g,Ju>=0. The first bound proves closed range; the Hilbert orthogonal-complement theorem then supplies the actual range preimage used by Cauchy–Schwarz. No formal differential-adjoint domain or final physical gap is assumed.

The intended half-line instantiation uses D=H¹_0(0,infinity), J the actual value embedding, A=d/dr−1/r+Z and B=−d/dr−1/r+Z. Its domain, Hardy multiplication, pairing, square identities and ODE kernel still need actual Lean proofs. The abstract helper alone does not discharge them. Strict one-declaration audit: audits/formal_semantics/20260910T015257_546372Z/receipt.json.

## Reproduction and remaining work

Development builds reuse pinned library and prior-audit objects. They use Lean4.34.0-rc2 at compiler commit6a10ac8c22beadecabdbb0919c2b50214762f91d and mathlibd9ed2b07e3d851ae48dbfe62550f6da9a1c128c9. Separate desktop source rebuilds started with no copied dependency objects; subsequent bounded segments reused only their own source-built objects. The 145-target sealed pass is logs/reproduction/SOURCE_REBUILD_CHECKPOINT_v8.md. Its stable 192-target supplement has also reported all compilations passed; final inventory and seal were still being collected at this checkpoint. The compiler and core were reused rather than bootstrapped. The newest finite-defect and partner-gap modules are outside that capsule.

The next physical path is the hydrogen complement, tensor/Pauli comparison and exact two-electron trial integrals. Ground symmetry, decay and the reviewed analytic/dictionary chain then need formal composition, followed by original moment arithmetic, residual certificates, solver termination and operational bit complexity. None of these obligations is replaced by the conditional theorem above. The original exponents 2256 and 1/16 remain claims to verify; the separately proved paper approximation exponent 1/3 has its own explicit physical prerequisites and no executable coefficient claim.

All files are new continuation artifacts. Frozen RWA_REPORT.md SHA2562545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066, commit166f43f2f0178f92d8c4d1dde209ef0eeaefa660 and tagtheorem-t-proof-freeze-2026-09-09 remain preserved. No novelty claim is made for classical hydrogen or spectral mechanisms.
