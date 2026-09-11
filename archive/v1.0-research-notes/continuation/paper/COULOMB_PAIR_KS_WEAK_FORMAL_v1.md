> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Actual two-electron pair KS weak equation, version 1

The new Lean result establishes the pair-collision weak equation for actual weak H² Coulomb eigenfunctions, including compact tests crossing the selected collision fiber. An actual scalar or full fermionic eigen-equation is the input. No binding, simplicity, existence or spectral gap is inferred.

The exact chart is θ(y,t)=(t+K(y)/2,t−K(y)/2), where |K(y)|=|y|². The existing Euclidean spectator space represents the unscaled physical center t=(x₀+x₁)/2; `pairCenterEquiv` is a proved linear isometric and measure-preserving identification. The Hessian trace identity is

    (Δ_y+|y|² Δ_t)(g∘θ)=2|y|² ((Δ_x₀+Δ_x₁)g)∘θ.

Thus the actual Coulomb eigen-equation gives c=1 and

    B(y,t)=4+4|y|²(−Z/|t+K(y)/2|−Z/|t−K(y)/2|−E).

The open coefficient patch excludes both nuclear zeros and permits y=0 whenever t≠0. B is smooth on that patch, with B(0,t)=4. For every real smooth compact test φ supported in the patch, the final theorem proves both actual product-volume integrability and

    ∫[−Δ_y φ−|y|² Δ_t φ+Bφ](g∘θ)=0.

The proof composes an actual continuous representative pointwise, derives the classical equation off y=0 from the physical Hamiltonian graph, applies the proved local weighted integration-by-parts identity, and removes the codimension-four fiber using continuous local-coefficient removability. It assumes no derivative of the representative at the pair collision. This route never pulls an arbitrary L² equivalence class through a dimension-changing map and requires no separate singular Jacobian formula.

The full-spin theorem uses one simultaneous representative family, preserving the common almost-everywhere identity, the pointwise simultaneous spatial/spin fermionic permutation law, and the inherited square-sum bound. It establishes the weak equation for every component.

The 11-module unit has 41 audited declarations: generic real-c principal/IBP/kernel support, exact pair geometry and weighted Laplacian, coefficient/patch, actual scalar classical/weak equations, and full-spin wrapper. The final six-module strict v5 audit includes the same-line attributed `pairCenterEquiv_apply` helper. All expanded statements compile with complete axiom reports, no printer ellipses, and only propext, Classical.choice and Quot.sound. The companion checkpoint binds source/object/development/strict evidence and focused independent review.

Development compilation reused pinned dependency objects; this unit has no isolated source rebuild. Successful and frozen artifacts remain unchanged. The unexecuted pair-specific auditor draft is preserved and superseded by root-reviewed shared v5.

This discharges the unscaled actual N=2 pair KS weak-equation portion of R03. It does not cover the triple nuclear/pair intersection, uniform factorial estimates, the global dictionary, or full Theorem T. Root separately owns the scalar/spin local-H² composition. Next is the actual ε-scaled nuclear/pair weak equation and normalized-difference forcing; physical dilation scales both attraction and electron repulsion and cannot silently be replaced by a charge-only family change.

Frozen historical source: `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md`, SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Historical claims are unchanged.
