> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Formal semantic supplement 002 — intended-domain density and convolution

This completed supplement extends the original formal semantic review, SHA-256 `19f9ca0823a8b2e072978b1acc8cc1efc9eb1e17b89451be2c4962de30117364`, and supplement 001, SHA-256 `c6792fb511294117d83e35a423e099e90ec434d338d2cbc82c0fc8261ef48cc5`. Both prior records remain unchanged.

## Strongest new result

**The actual intended fermionic weak H² domain is dense in the actual fermionic L² space, for every finite electron count N.** The exact accepted statement is

`TheoremT.Continuum.fermionic_weakH2_dense (N : ℕ) :`
`Dense {ψ : FermionicSpace N | ∀ σ, HasH2 (ψ.val σ)}`.

The subtype already supplies the original full simultaneous space-and-spin antisymmetry condition. The displayed domain is therefore the original `targetDomain` viewed inside that subspace. It is not a newly defined surrogate Sobolev space. This is a fully formalized theorem about density in the inherited L² topology.

The proof has three independently checked steps:

1. `SmoothL2Density_v2` applies the pinned mathlib smooth-compact Lp approximation theorem to the actual complex Lebesgue L² configuration space. The prior classical-to-weak bridge shows these smooth compact representatives belong to the original all-mixed-derivative H² domain. Thus actual spatial H² functions are L²-dense. Finite-spin density uses the product/PiLp homeomorphism, with the original finite spin index set.
2. `FermionicAction_v2` constructs the original simultaneous coordinate/spin action as continuous complex linear maps, proves its actual multiplication convention `U(π*τ)=Uπ Uτ`, and twists it by the permutation sign. The invariant submodule of that signed representation is proved equal to the existing `fermionicSubspace`; antisymmetry is not assumed through a new interface.
3. `FermionicDensity_v2` uses the explicit group average

   `Pψ = (|S_N| : ℂ)⁻¹ • Σπ sign(π) • Uπψ`.

   The group cardinal is nonzero, including N=0. Membership in the fermionic space, identity on fermionic inputs, and continuity of P are proved. Earlier actual derivative covariance and linearity prove that P preserves componentwise weak H². The induced map into the fermionic subtype is continuous and surjective. Applying it to the dense componentwise H² set proves the displayed density theorem.

There is no inference that intersection with a closed subspace preserves density. No orthogonality or norm-one assertion about P is needed for this argument or claimed by these modules. Neither dense subspaces nor averaging require a binding, ground-state or spectral-gap premise.

The earlier L² approximation declarations are mathematical existence statements. They provide no finite encoding, coefficient algorithm, approximation rate, original-dictionary approximation theorem or bit-complexity bound.

## Convolution results and representative fidelity

**Actual weak derivatives commute with smooth compact-kernel convolution.** `HardyWeakConvolution_v1` defines, for an original spatial L² equivalence class f,

`mollify η f x = ∫ y, η(x-y) • f(y)`.

For real smooth compactly supported η, it proves this is a globally smooth complex-valued function on the original `Configuration N`. If `WeakPartial f g k`, it proves pointwise, for every x,

`fderiv ℝ (mollify η f) x (coordinateVector k) = mollify η g x`.

L² local integrability and compactness of the translated kernel justify convolution differentiation. Testing the weak derivative against η(x−y) introduces a minus sign in its y derivative; this cancels the minus sign in the distributional integration-by-parts relation. The resulting derivative sign and convolution orientation are correct.

**Localized convolution is an actual smooth compact function.** `HardyWeakConvolution_v2` first applies the previously verified `cutoffMul` and then mollifies. Its compact-support proof replaces the chosen L² representative almost everywhere by the raw product χ(y)f(y), which really vanishes outside the compact support of χ. Almost-everywhere equality gives equality of the convolution integrals at each x. Thus the proof does not incorrectly assume that the arbitrary representative selected for an L² equivalence class has compact support.

`mollify_cutoff_smooth_compact` proves actual smoothness and compact support for every original L² input, given a real smooth compact kernel and a continuous compact cutoff. `mollify_cutoff_derivative` supplies the correct mollified Leibniz expression `χg+(∂ₖχ)f` when χ is smooth and g is the actual weak derivative.

No kernel positivity or unit-mass hypothesis is needed for these exact smoothing identities. Consequently these modules alone do not prove L² contraction, approximate-identity convergence, or convergence of the function and its derivatives in a Sobolev norm. Compactness of η alone would not make η*f compactly supported for arbitrary f; the verified compact-output theorem explicitly includes the cutoff. The mathematical Bochner integral definition is not an executable numerical convolution procedure.

## Accepted evidence and unchanged frontier

Two independent expanded-statement/axiom runs exited zero:

- `formal_semantics/20260909T232006_821987Z/receipt.json`: 28 declarations from `SmoothL2Density_v2`, `FermionicAction_v2`, `HardyWeakConvolution_v1` and `HardyWeakConvolution_v2`.
- `formal_semantics/20260909T232015_572332Z/receipt.json`: 12 declarations from `FermionicDensity_v2`.

Every one of the 40 requested axiom-dependency outputs appeared. All audited source and object hashes were unchanged during the run, and no forbidden source token or unexpected axiom was found. Recursive dependencies use only `propext`, `Classical.choice`, and `Quot.sound`. This includes private helpers and the local invertible-cardinality instance through the public declarations that depend on them. Counts include definitions as well as theorems.

The compiler and cache boundary are unchanged: pinned Lean 4.34.0-rc2, existing pinned dependency objects and previously compiled new proof objects, with final sources compiled by their producing branches. These audit runs are not a complete isolated dependency-source rebuild. Exact hashes, coverage, and the byte-identical copies of the successful convolution objects into the common continuation build directory are recorded in `FORMAL_SEMANTIC_SUPPLEMENT_002_MANIFEST_v2.json`.

The historical frozen path, source SHA-256, commit and tag, and the exact unchanged physical-definition source are those cited in the original review. No frozen source or sealed prior review was altered. This supplement accepts only the five modules listed above; later quantitative-cutoff or probability-kernel files require their own review.

The new density theorem does **not** yet establish dense definition of the current Coulomb partial operator: its domain still includes the additional undischarged Coulomb-product L² condition. Nor is the displayed density an H² graph-norm core theorem, an H¹ approximation theorem, or an operator self-adjointness theorem. Weak-H¹ Hardy extension, configuration slicing, quantitative Coulomb/Laplacian bounds, F02 completion, F03, F04 and full Theorem T remain open in this accepted source set.
