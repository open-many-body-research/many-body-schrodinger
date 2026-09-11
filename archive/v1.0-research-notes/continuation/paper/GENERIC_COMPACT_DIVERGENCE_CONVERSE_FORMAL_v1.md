> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Compact tests for L² plus divergence forcing, version 1

Let E be any finite-dimensional real inner-product space with its actual Lebesgue measure; let f,a and bᵢ be actual complex L² classes, with finitely many arbitrary fixed directions vᵢ. Assume every real C∞ compact test φ satisfies

∫(Δφ)f = ∫φa − Σᵢ∫(D_vᵢφ)bᵢ.

Then the actual tempered-distribution equation is Δf = a + ΣᵢD_vᵢbᵢ. No derivative, Sobolev regularity, or density premise is imposed on f or bᵢ. The finite directions need not form a basis; the separate Euclidean Laplacian is expanded in a genuine orthonormal basis.

The proof first extends the identity to complex compact tests by real and imaginary parts. Explicit scaled cutoffs then tend to one in actual Schwartz/L² pairings through order two, as proved in the separately sealed generic compact-distribution-converse checkpoint. Finite sums and uniqueness of limits give the identity on every Schwartz test and hence the tempered equation.

This is the exact forcing class needed for a cutoff local elliptic H¹ bootstrap from only local L² information: Δ(ηu) can be represented as an L² term plus divergences of L² terms without assuming first derivatives of u. The bootstrap and local H² result are separate obligations.

Evidence: GenericCompactDivergenceTests_v1 and GenericDistributionDivergenceConverse_v1 compile; strict audit 20260910T165206_899344Z verifies both exact final statements and complete standard-axiom dependencies. Only propext, Classical.choice and Quot.sound occur. No additional mathematical axioms, proof placeholders, or extra trust mechanism occur. Development compilation reuses pinned library, prior-audit and continuation objects. These sources are outside the successful 671-target desktop source snapshot.

No quantitative estimate, local Grushin gain, analyticity, executable derivative selection, full Theorem T, or novelty is claimed here. New continuation files only; the frozen lineage remains commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. Frozen RWA_REPORT.md SHA-256: 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066.
