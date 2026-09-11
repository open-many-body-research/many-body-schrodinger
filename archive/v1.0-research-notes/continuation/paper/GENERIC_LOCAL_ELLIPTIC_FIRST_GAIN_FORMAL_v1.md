> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# A local first-order elliptic gain from L² data

Evidence category: fully formalized mathematical implication, with the actual
compact-test Laplacian equation as hypothesis. This is a prerequisite for the
nested-cutoff H² argument. It is not a weak Grushin estimate or an analytic
regularity theorem.

Let E be any finite-dimensional real inner-product space, equipped with its
actual Lebesgue measure, and let Ω be any subset of E. Suppose f,w:E→ℂ satisfy

    ∫ (Δφ) f = ∫ φ w

for every real C∞ compactly supported test φ whose topological support is
contained in Ω. Let χ be real, smooth and compactly supported in Ω, and suppose
f and w belong to L² on K=tsupport χ. Then there are actual L² functions U,A,Bᵢ,
for any finite orthonormal basis eᵢ, with the almost-everywhere identities

    U = χf,    A = χw − (Δχ)f,    Bᵢ = 2(Dᵢχ)f,

and the actual tempered-distribution identity

    ΔU = A + Σᵢ DᵢBᵢ.

Moreover, U has L² weak first derivatives in every direction. Explicitly, there
is d:E→L²(E;ℂ) such that for every v and every real smooth compact test φ,

    ∫ φ d(v) = −∫ (Dᵥφ) U.

The theorem does not assume first derivatives of f, and does not assume global
integrability of either raw input. Restricting the hypotheses to K is possible
because the proof constructs actual indicator extensions 1_K f and 1_K w in
L² and proves that all needed test pairings agree. The support inclusion
support(Δφ)⊆tsupport φ is proved from the finite directional derivative formula.

The localization calculation tests the original equation with χφ. Expanding
Δ(χφ), regrouping its three terms, and proving their integrability gives the
displayed divergence formula. The converse from compact tests to the actual
tempered identity uses the separately verified
GenericDistributionDivergenceConverse_v1 module.

The regularity step uses the exact Fourier convention exp(−2πi⟨x,ξ⟩). Its Bessel
operator satisfies J²U=U−(2π)⁻²ΔU. Thus, for every real s, U∈Hˢ and ΔU∈Hˢ imply
U∈Hˢ⁺². Here U,A,Bᵢ are in H⁰, each DᵢBᵢ is in H⁻¹, and hence U∈H¹. Existing
formalized Sobolev-to-weak-derivative results yield the stated L² witnesses.
Finite dimension zero and an empty orthonormal basis are included.

A further lemma transfers the local equation from f to U=χf on any subset
S⊆Ω where χ equals one. This supplies the exact locality fact needed for the
second cutoff. No regularity hypothesis is hidden in that transfer.

The sources are GenericNegativeSobolevGain_v1,
GenericCompactLaplacianProduct_v1, GenericCutoffLaplacianDivergenceTests_v1,
GenericLocalCutoffLaplacianTests_v1, GenericLocalEllipticFirstGain_v1, and
GenericCutoffPlateauLaplacian_v1. The adjacent checkpoint records their hashes,
compiled objects and strict expanded-statement/axiom receipts. Only propext,
Classical.choice and Quot.sound occur. The L² witnesses are mathematical
existence objects; no executable differentiation algorithm is claimed.

Development compilation reused the declared pinned Mathlib, prior-audit and
continuation objects. These six modules are later than, and outside, the
671-target desktop source-rebuild snapshot. No new source-rebuild claim is
made here. There is no claim of a quantitative estimate, novelty, completion
of the local H² bootstrap, weak Grushin gain, or full Theorem T.

The frozen project is preserved: original relative path RWA_REPORT.md,
SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066,
commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, annotated tag
theorem-t-proof-freeze-2026-09-09. This continuation changes none of its bytes
or inherited claim statuses. The next active obligation is the second,
nested-cutoff gain yielding actual local weak H².
