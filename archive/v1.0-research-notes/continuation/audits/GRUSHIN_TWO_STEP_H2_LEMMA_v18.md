> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Joint H² after two tangential gain steps

2026-09-10. Evidence: **paper corollary, conditional on the rigorously described weak local gain being established**. This note specifies a useful smaller formal milestone; it is not a Lean verification. It supplements `GRUSHIN_PARTIAL_MOLLIFICATION_REVIEW_v18.md`, SHA-256 `3464cbf5b9fa1a34283993441cd40905b9334c830c47555a84fd09403480cdd8`.

Let c>0, y∈R⁴, t∈Rᵐ, m≥1, Q=−Δ_y−c|y|²Δ_t+B, and let the five nested product boxes Ω₀,…,Ω₄ have the cutoff bounds used in the preceding review. The one-step weak local estimate is assumed available on Ω_j→Ω_{j+2}, j=0,2, with common constant

    L=(1+b₀)G,

where b₀ bounds ||B||∞ and G is either the original valid H3 constant or the explicitly proved improved constant from that review. All data are taken on Ω₀, so the same constants apply after restriction.

Suppose v,f∈L²(Ω₀), Qv=f in distributions, B∈L∞(Ω₀), and all first tangential weak derivatives ∂_{t_a}B lie in L∞(Ω₀). Assume all first tangential weak derivatives ∂_{t_a}f lie in L²(Ω₀). No y derivative of B or f is needed for this corollary. Set

    W=||v||₂,
    F₀=||f||₂,
    F₁=max_a ||∂_{t_a}f||₂,
    K_t=max_a ||∂_{t_a}B||∞,
    C₀=L(W+F₀),
    C₁=L[C₀+F₁+K_t W].

Then v∈H²(Ω₄) in the ordinary joint weak Sobolev sense, and

    ||v||_{H²(Ω₄)} ≤ sqrt((m+5)(m+6)/2) C₁.             (T2)

The Sobolev norm in (T2) sums squares once per multi-index of total degree at most two. The dimensional factor is the square root of binom((4+m)+2,2). If an ordered-Hessian convention is used instead, the norm and combinatorial factor must be changed accordingly.

Proof. The first gain on Ω₀→Ω₂ produces v, its first y/t derivatives, and all second y derivatives, with each component norm bounded by C₀. For each a, w_a=∂_{t_a}v is therefore an actual L² weak derivative on Ω₂. The weak product rule gives the exact equation

    Qw_a = ∂_{t_a}f − (∂_{t_a}B)v =: g_a,

and ||g_a||_{L²(Ω₂)}≤F₁+K_t W. The needed product rule holds along t slices for bounded B with bounded weak t derivatives and v with first weak t derivatives; it does not require v to be jointly H² in advance. Tangential differentiation commutes with P_c distributionally because its coefficients depend only on y.

Apply the same weak gain to w_a on Ω₂→Ω₄. Every ∂_{t_b}w_a and every ∂_{y_i}w_a has norm at most C₁. These are exactly all pure t second derivatives and all mixed y/t derivatives of v. Weak mixed derivatives commute distributionally, so they furnish the standard H² derivatives. The previously established second y derivatives remain bounded by C₀ after restriction. Since L≥1, C₁≥C₀≥W. Thus every multi-index derivative through order two has norm at most C₁, and summing proves (T2).

The proof is triangular and uses four fixed gaps. In each application of the weak gain, regularize the complete forcing P_cw=g−Bw, not B and w separately. The auxiliary fixed-radius functions may be justified in joint H² by the ordinary Laplacian relation, but their nonuniform derivative norms are discarded. This corollary establishes joint H² only after the second gain, consistent with the preceding explicit obstruction to a one-step conclusion.

The full H12 theorem needs the longer previously specified schedule. This smaller result does not replace its higher derivative accounting or imply analyticity. Its formal prerequisites are the actual one-step weak gain, finite tangential weak Leibniz rule, and identification/commutation of distributional derivatives. Existing smooth compact estimates alone do not constitute a formal proof of this corollary.

All artifacts are new continuation files. Frozen provenance remains commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`, frozen `RWA_REPORT.md` SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
