> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# R24: actual weak profile to classical pointwise bounds

The fully formal local embedding now constructs compatible smooth representatives of genuine weak derivatives on the physical product `EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ (Fin 3)`. The ordinary product norm and its Lebesgue measure are retained.

Fix one natural-index family F whose every entry is locally L² on an open region Ω, with actual weak coordinate identities ∂Yi Fαβ = F(α+ei)β and ∂Tj Fαβ = Fα(β+ej). Fix a smooth compact cutoff supported in Ω that equals one on an open plateau. A closed seven-coordinate box K, transported by the literal measure-preserving equivalence `sevenToProduct`, lies in this plateau and in a region ΩN. Let U be any open subset of K. Assume actual `FactorialLocalMemLp F ΩN r` at every finite r.

For `N_r = factorialLocalProfile F ΩN r`, the theorem constructs one function v on the physical product, smooth on `sevenToProduct(U)`, with F00 = v almost everywhere there. Every ordered coordinate word of v is almost everywhere the corresponding counted natural-index entry of the same F. For every word w and point x in that open image,

`|D_w v(x)| ≤ Ebox(K) N_(length(w)+11)`.

The exact geometric constant is `Ebox = product_i (Li^(-1/2) + Li^(1/2))`, where Li > 0 are the seven side lengths. For four equal Y lengths Ly and three equal T lengths Lt it is `(Ly^(-1/2)+Ly^(1/2))^4 (Lt^(-1/2)+Lt^(1/2))^3`. It is independent of derivative order and of F. If F00 is already continuous on the open image, the bound and smoothness hold for F00 itself, pointwise.

The proof forms the actual finite Leibniz words of the compactly supported cutoff. All such fields are proved global L² weak derivatives of one cutoff base. Their genuine mollifications converge strongly in L². The proved tensor FTC inequality turns convergence of the 128 mixed fields into uniform convergence. Uniform limits of the actual coordinate derivatives give a genuine Fréchet derivative, and finite induction at every order gives one smooth compatible family. Exact measure-preserving transport returns this representative and all its word derivatives to the physical product.

The quantitative constant is preserved through the limit: each finite group of approximating L² norms is eventually bounded by the limiting bound plus ε/Ebox, and ε is removed after passing to the uniform limit. Thus no uniform norm bound on arbitrary chosen representatives or on cutoff approximants is assumed. The zero outer index in the actual 498-term norm supplies the unweighted derivative norm. A word of length k costs at most k+4; a tensor subset adds at most seven letters. This proves the exact k+11 reserve. Actual MemLp is established before every real extended-norm interpretation.

The primary endpoints are `grushin_actual_profile_smooth_representative` and `grushin_actual_profile_continuous_base`. The latter has the explicit continuity hypothesis only for F00; higher classical regularity and all pointwise derivative bounds are conclusions.

This is the local weak R24 embedding. The concrete raw weak PDE/physical KS application must still supply the named family, weighted profiles, and actual box/cutoff geometry and then combine the profile bound with the scalar factorial recurrence. No full Theorem T, KS descent, global H² approximation, numerical energy interval, executable algorithm, or complexity bound is asserted here. Existence of a representative uses standard classical choice and is not an algorithm.

All sources are new continuation files. Frozen historical reference: `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Pinned development object caches were reused; these new modules are outside isolated source rebuild v20.
