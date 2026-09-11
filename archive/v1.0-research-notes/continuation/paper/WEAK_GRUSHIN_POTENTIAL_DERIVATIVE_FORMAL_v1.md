> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local weak spectator product rule for a smooth potential

Let Y,T be finite-dimensional real inner-product spaces and Ω an open subset
of their ordinary Cartesian product. Let B be a real function that is C∞ on
Ω. Let f,d be actual complex L² classes on Y × T and assume d is the weak
directional derivative of f in direction (0,v), defined using all real smooth
compact joint test functions.

The theorem
`TheoremT.Continuum.weakProduct_spectator_local_potential_leibniz`
proves that Bf and Bd+(D_(0,v)B)f are locally L² on Ω, and that for every real
C∞ compact test φ supported in Ω both integrals in the following identity are
integrable and the identity holds:

    ∫ φ [Bd+(D_(0,v)B)f] = −∫ (D_(0,v)φ) Bf.

This is the actual local weak Leibniz rule. Global L² membership of Bf is
neither assumed nor asserted. Smoothness or even measurability of the chosen
total function B outside Ω is not required. The local derivative is the actual
Fréchet derivative on Ω, where differentiability has been established.

For the test identity, φB is proved globally C∞ and compactly supported.
Where φ has nonzero topological support, smoothness follows from that of B
on Ω. Outside this support the product is locally zero. The same reasoning
applies to φ DB and (Dφ)B. Their compact support and the local integrability
of L² functions prove every required Bochner integrability statement. The
product derivative formula is proved at points in the test support using
ordinary differentiability; outside the support, φ, Dφ and D(φB) vanish.
The input weak derivative identity applied to φB then yields the formula.
No differentiation of an indicator is used.

For local L² membership, every compact K⊆Ω admits a smooth compact cutoff η
with support in Ω and equal to one in a neighborhood of K. The globally smooth
compact coefficient C=ηB agrees with B and its directional derivative on K.
Both C and DC are bounded. Their restricted L∞ memberships pass to B and DB
by equality on K, and multiplication of restricted L² functions gives the
claimed local L² bounds. The shared coefficient lemma is formulated for any
Borel measure on a finite-dimensional real normed space.

The modules are `WeakGrushinPotentialDerivativeTest_v1.lean`,
`WeakGrushinPotentialDerivativeLocalL2_v1.lean`, and
`WeakGrushinPotentialDerivative_v1.lean`. They contain six declarations in
total. Exact sources compile and strict audits print complete expanded
statements and all axiom dependencies. Only propext, Classical.choice, and
Quot.sound are used. Existing pinned dependency objects are reused; these
sources are outside the completed 671-target desktop source-rebuild snapshot.

The input derivative relation is global for the L² witnesses f,d; the output
product rule is local on Ω. The theorem is a prerequisite for differentiating
the potential term in a weak Grushin equation. It does not itself establish
commutation of the principal operator with weak derivatives, a second local
regularity gain, analytic regularity, or full Theorem T. Those are separate
composition obligations.

Frozen historical reference: commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`,
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
Frozen and previously successful sources and receipts are unchanged.
