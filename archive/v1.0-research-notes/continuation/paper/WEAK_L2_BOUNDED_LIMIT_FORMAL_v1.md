> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Bounded weak derivative limits, version 1

Let E be a finite-dimensional real inner-product space with its Lebesgue measure. Suppose actual complex L² functions uₙ converge strongly to f in L². If gₙ is the genuine weak directional derivative Dᵥuₙ and ‖gₙ‖₂≤C for every n, there is a genuine weak derivative g=Dᵥf in L² with ‖g‖₂≤C. Weak derivatives are tested against every real C∞ compactly supported function. No convergence of gₙ or derivative-existence premise for f is assumed.

The simultaneous theorem preserves a single squared-norm bound for any finite family of continuous tempered-distribution operators Aᵢ. If Aᵢuₙ=dₙ,ᵢ∈L² and Σᵢ‖dₙ,ᵢ‖₂²≤C, then Aᵢf=gᵢ∈L² with Σᵢ‖gᵢ‖₂²≤C. Instantiating Aᵢ as actual directional derivatives gives the finite first-derivative result. Instantiating one family containing first derivatives and all ordered compositions gives compatible first and second weak derivative witnesses and preserves the combined bound

Σᵢ‖Dᵥᵢf‖₂² + Σᵢ,ⱼ‖DᵥⱼDᵥᵢf‖₂² ≤ C.

The proof uses the complex Hilbert dual. Banach–Alaoglu gives a cluster point inside the same dual norm ball, and the Riesz isometry gives a Hilbert-space vector with that norm bound. Every continuous-linear functional having a limit on the original sequence takes that limiting value on the selected vector. Applying this to Schwartz-test evaluation after the actual L²-to-tempered embedding identifies the derivative of the strong input limit. One application to the finite Hilbert product preserves an aggregate bound without multiplying by the number of components. No separability or subsequence hypothesis is needed; the proof does not assert convergence of every derivative sequence.

The genuine compact-test derivative identities are connected to tempered derivatives by the separately audited generic and product converse modules. For ordinary Cartesian products Y×T, exact lift/unlift through WithLp 2 preserves actual product Lebesgue measure, strong L² convergence, weak test identities and every output norm. The product uses its original maximum norm; the Euclidean copy is used explicitly.

The checkpoint records exact source/object hashes and strict expanded-statement/complete-axiom audits. Only propext, Classical.choice and Quot.sound are admitted. The construction provides mathematical derivative witnesses, not an executable algorithm. Development checks reuse pinned library, prior-audit and continuation objects; these sources lie outside the completed 671-target desktop source snapshot.

These theorems discharge a limit-passage prerequisite for partially regularized Grushin solutions. They do not establish the needed uniform Grushin estimates or commutation/convergence of the particular partial mollification procedure. They do not prove local Grushin gain, analyticity, factorial estimates, Theorem T, or a certified energy solver. No novelty claim is made.

All work is in new continuation files. Frozen lineage: commit 166f43f2f0178f92d8c4d1dde209ef0eeaefa660, tag theorem-t-proof-freeze-2026-09-09. Frozen RWA_REPORT.md SHA-256 2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066.
