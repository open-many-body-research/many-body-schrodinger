> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Local weak Grushin solutions: an actual weighted L² factorial estimate

Evidence category: kernel-checked local PDE theorem. This note states the new result and its limits; it does not claim a new literature result or completion of Theorem T.

Work is in the versioned continuation. The frozen composition target is `rwa_proof/THEOREM_T_COMPOSITION.md`, SHA-256 `1f60593d0d241738171c395e83d22fd439836b7e9cd3a685f97e16e632cb82da`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Its bytes and unresolved claims are preserved.

## Statement

Let Y∈R⁴, T∈R³, c>0, and

P_c = −Δ_Y − c|Y|²Δ_T.

On an open set Ω, let f be locally L² and solve (P_c+V)f=g against every real smooth compactly supported test function. V is real and g complex; both are smooth on Ω. Let a=(0,t₀). A closed rectangle with half-widths a_Y,a_T lies in Ω; choose strictly smaller positive half-widths b_Y,b_T and 0<ρ≤1 with ρ<b_Y,b_T. The inner rectangle is Q₀ and Q_s has half-widths b_Y−s,b_T−s.

Assume a genuine weak H¹² family for f on Q₀ with squared L² budget W for each derivative. This is the literal `ProductMixedMultiIndexWeakHk` predicate, including actual weak derivative identities. Assume A≥1, M,F₀≥0 and, for each word w of physical coordinate directions,

|D_w V| ≤ M A^|w| |w|! on Q₀,

and D_w g is in L²(Q₀) with squared integral at most (F₀ A^|w| |w|!)². These are bounds on the known coefficient and source, not on the solution's unknown higher derivatives.

Let C₁,C₂ be global bounds for the first and second derivatives of the actual smooth transition used by the cutoffs. Put

S=max(1,2b_Y),
C₀=498 S²(4b_Y²+2b_Y+2+2/c),
K₁=(8/3)C₁(8/(b_Y−ρ)²+6|c|),
K₂=(32/9)(C₂+C₁²)(4/(b_Y−ρ)²+3|c|),
C=max(1,C₀(1+2M+6|c|+K₁+K₂)),
B=2CA, and H₀=498 S²√W.

There exists one coherent family F_{α,β} of actual mixed weak derivatives, with F_{0,0}=f, chosen before every derivative order. All its finite-order local L² budgets and coordinate weak derivative identities hold.

For a base index (α,β), use cost |α|+|β|+min(|α|,4). Its outer norm is the sum of the actual restricted L² norms of

Y^γ F_{α+u,β+v}

over the exact 498 triples satisfying |u|+|v|≤2 and |u|+2|v|−2≤|γ|≤2. Let P_r(s) be the finite maximum of this outer norm over bases of cost at most r. Every field entering the maximum is proved L² before its extended norm is interpreted as a real number. Then, for every natural r,

P_r(ρ) ≤ 6B(F₀+H₀)(6B/ρ)^r r!.

All displayed constants precede r. The actual transition bounds C₁=96 and C₂=14016 are available from a separate formal proof; the paper's different cutoff constants have not been substituted silently.

## Proof dependencies

1. Qualitative finite-order weak regularity follows from the original local equation. Local weak uniqueness identifies independent finite choices and constructs one coherent all-order derivative family.
2. The exact mixed differentiated equation, its potential terms and quadratic principal commutator are derived from that family and the original equation.
3. Genuine compact weak H² cutoffs and their principal outputs are constructed. Their output estimates use literal local profiles, with all required L² representatives constructed from actual budgets.
4. The compact weak 498-term graph estimate and local weak uniqueness on the cutoff plateau bound the actual inner outer norm. Taking the exact finite maximum introduces no extra cardinality factor. This proves the localized recurrence with C independent of r and the gap.
5. The actual finite H¹² budget bounds all starting profiles of cost at most eight by H₀. Actual domain monotonicity and the proved scalar recurrence give P_r(ρ)≤2B(F₀+H₀)(2B(r+1)/ρ)^r.
6. A nonnegative term in the exponential series proves (r+1)^r≤3^(r+1)r!, including r=0. Substitution yields the stated factorial bound. The proof never divides by F₀+H₀.

## Verification and limits

The final exact declarations are `local_weak_grushin_raw_profile_bound` and `local_weak_grushin_raw_factorial_bound`. Their source hashes, strict expanded statements, axiom reports, dependency checkpoints and independent reviews are in `audits/LOCAL_WEAK_GRUSHIN_RAW_FACTORIAL_CHECKPOINT_v1.json`, SHA-256 `4e98a5f84c6b82ec683c1a809582969b869ada06695c17775534b39ff1d1941b`.

The trusted axioms are propext, Classical.choice and Quot.sound. Pinned Lean/Mathlib development objects were reused; these new sources are outside isolated rebuild v20. Mathematical choice of representatives supplies no executable algorithm.

The result currently supplies weighted L² estimates. Physical chart transport, a compatible smooth representative and pointwise bounds are separate active obligations. KS descent, global H² approximation in the exact trial dictionary, correctness and termination of the rational solver, operational bit complexity and full Theorem T remain unresolved. The exponents 2256 and 1/16 have not been verified by this theorem.
