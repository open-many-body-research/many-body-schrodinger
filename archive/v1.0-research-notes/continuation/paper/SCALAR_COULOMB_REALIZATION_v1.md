> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual scalar Coulomb realization and ground-energy identification

Evidence category: **Lean-verified mathematical result in the pinned development environment**. Ten exact final modules and 66 complete expanded-statement/axiom reports pass. Pinned dependency objects were reused; these new modules are outside the previously completed 192-target isolated source rebuild. No new mathematical axiom, `sorry`, `sorryAx`, `native_decide` or compiler trust extension supplies a proof.

For each finite electron count N and every real Z, let the scalar Hilbert space be the actual complex L² space on (R³)^N, with Lebesgue measure. It imposes no permutation or spin restriction. Define the scalar Hamiltonian by its actual weak differential graph

    H = -1/2 sum_i Delta_i - Z sum_i 1/|x_i|
        + sum_(i<j) 1/|x_i-x_j|.

The operator has exactly the independently specified weak H² domain, is densely defined, symmetric, closed and self-adjoint. Its weak H¹ quadratic form is

    q[f] = 1/2 sum_k ||partial_k f||²
           + integral V(x) |f(x)|² dx.

The potential integral is integrable for every actual H¹ input. Existence and uniqueness of the form value hold exactly on H¹; the definition does not add an H² or hidden Coulomb-integrability premise to that domain.

There is a finite real E such that the normalized H² graph infimum, normalized H¹ form infimum, and bottom of the actual scalar operator spectrum all equal E. Moreover

    -N (max(Z,0))²/2 <= E <= 0,
    E <= the original full-spin fermionic ground-energy infimum.

E belongs to the scalar spectrum, every spectral point is real, and none lies below E. The spectrum is defined by failure of a bounded two-sided inverse into the actual operator domain; reality is proved, not imposed by the definition. The result does not assume or assert ground-state attainment, binding, simplicity, a gap or a normalized ground-state vector.

## Proof and formal interface

`ScalarCoulombOperator_v1.lean` makes the existing literal scalar weak Coulomb graph into a partial linear map. Previously proved weak-H² multiplication, graph uniqueness and scalar smooth density establish its exact domain and dense definition. Existing weak integration by parts establishes symmetry.

`ScalarCoulombSelfAdjoint_v1.lean` uses the actual Fourier multiplier free resolvent R_mu of `-Delta/2+mu`. On its range, the operator error is exactly V R_mu and obeys

    ||V R_mu|| <= 2 (|Z| N + choose(N,2)) / sqrt(2 mu).

Choosing `mu = 1 + 8 C²`, where `C=2 (|Z| N + choose(N,2))`, makes this error smaller than one. The previously verified generic bounded-error inverse construction supplies a surjective real shift. Dense definition and symmetry then give actual self-adjointness. No spectral premise or fermionic-space restriction is used to provide the scalar operator.

`ScalarCoulombVariational_v1.lean` identifies its finite normalized graph infimum with the greatest quadratic operator lower bound. A concrete existing nonzero scalar H² trial establishes finiteness above; nuclear completion of squares gives the sharp elementary lower bound. `ScalarCoulombSpectral_v1.lean` applies the verified general unbounded resolvent arguments to identify the least spectral point and exclude nonreal spectrum.

The four `ScalarCoulombForm*.lean` modules define and identify the actual weak H¹ form. A proved smooth compact H¹ graph sequence and the quantitative Coulomb multiplier estimate transfer operator lower bounds to the H¹ form. Conversely the form identity applies directly to each actual H² graph input. Their normalized infima therefore agree. The same convergence proof transfers any explicitly supplied comparison

    beta ||f||² <= q[f] + C |l(f)|²

between the H² operator domain and the H¹ form domain, for every bounded complex scalar functional l and real beta,C. This equivalence does not prove a hydrogen complement or physical rank-one comparison.

`ScalarFermionicEnergyComparison_v1.lean` sums the scalar quadratic lower bound over the actual spin components of a fermionic graph input. Normalization then proves the scalar energy is at most the original fermionic energy. The previously proved nonpositivity of that fermionic infimum yields E<=0, including N=0.

The final exact theorem is

    TheoremT.Continuum.scalar_coulomb_continuum_foundation
        (N : Nat) (Z : Real)

in `ScalarCoulombFoundation_v1.lean`. It has no analytic, spectral, attainment or comparison hypotheses. Its exact source SHA-256 is `da4c0b215a86116b440dfb0333cf40b4218d9995b32baa1e303fb7e2dcc4c241`.

## Application and remaining boundary

This theorem supplies the scalar realization premises explicitly retained in `paper/TWO_ELECTRON_PHYSICAL_COMPARISON_v1.md`, reviewed here at SHA-256 `9956d7cc34ddd95dc4a283bdd416dc8fe718e6701b9ceff93975dd3c92c1afa6`. The actual scalar operator at N=2 has the exact Hamiltonian, domain and form used there. The separate already verified fermionic realization supplies its full-spin counterpart.

The physical hydrogen complement, tensor/slicing projections, exact fermionic joint projection, two-electron product-trial moments and their rank-one instantiation retain their own formal obligations. Neither this scalar realization nor an equality between its form and spectral energies proves equality of scalar and fermionic energies; only the stated one-sided inequality is established here. Full Theorem T remains unverified.

Strict semantic/axiom receipts are `audits/formal_semantics/20260910T024106_704009Z/receipt.json` (38 declarations), `20260910T024210_790694Z/receipt.json` (25 declarations), and `20260910T024303_141040Z/receipt.json` (3 declarations). All have complete axiom reports, zero printer ellipses and unchanged final source/object hashes. Independent exact-source reviews are `audits/SCALAR_OPERATOR_FORM_AGENT_REVIEW_v1.json` and `audits/SCALAR_COULOMB_FORM_INDEPENDENT_REVIEW_v1.json`. These reviews supplement the proofs; agreement is not a proof mechanism.

Frozen provenance: commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`; frozen target `THEOREM_T_FREEZE_2026-09-09_212604/rwa_proof/RWA_THEOREM.md`, SHA-256 `d13f655a98cd278115924af4f0597991619fce0345f81e17151c1524229e8f09`. This new scalar realization is a separately identified mathematical model and leaves the original fermionic target, dictionary and all frozen artifacts unchanged. No novelty claim is made.
