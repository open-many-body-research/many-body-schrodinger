> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Physical scalar and fermionic-spin nuclear KS one-step gain

Four compiled modules apply the proved local weak Grushin gain to the actual
scalar Coulomb graph and to its full fermionic spin-space graph. This is a
conditional regularity theorem for graph solutions at energy E; it does not
assert existence, normalization, binding, spectral isolation or uniqueness of
such a solution.

The physical graph uses the continuum configuration space R^(3N), kinetic
term −½Σ_iΔ_i, nuclear potential −ZΣ_i|x_i|⁻¹, and repulsive pair potential
Σ_(i<j)|x_i−x_j|⁻¹. Its domain condition consists of actual first and all mixed
second weak L² derivatives. The spin space includes all functions from the
N electron labels to two spin labels. Fermionic symmetry simultaneously
permutes spatial coordinates and spin labels.

For a selected electron i, the concrete nuclear KS lift replaces only x_i by
the quadratic KS map of y∈R⁴ and retains all 3(N−1) spectator coordinates t.
It satisfies |x_i|=|y|². The coefficient patch Ω_i requires every unselected
electron position to be nonzero and every pair of electron positions to be
distinct. The selected nuclear collision y=0 is allowed. Simultaneous nuclear
collisions, electron-pair collisions and their intersections are not covered
by this patch.

The exact lifted equation is

    [−Δ_y−4|y|²Δ_t+B_i] (g∘L_i)=0,
    B_i=−8Z+8|y|²(V_without_selected_nucleus∘L_i−E).

The factor 4 follows from the proved KS principal identity. The factor 8 in
B_i combines it with the physical kinetic factor ½. B_i is analytic on Ω_i
and equals −8Z at y=0. The previous weak-pullback theorem supplies the equation
across this selected nuclear collision; the present application does not
enlarge the coefficient patch.

For every real C∞ compact cutoff χ supported in Ω_i, the scalar theorem
`scalar_coulomb_nuclear_KS_one_step` fixes a compact K and C≥0 with
tsupport χ⊆K⊆Ω_i before the scalar graph solution f and its continuous
representative g. It constructs an actual product-L² class U equal almost
everywhere to χ(g∘L_i), together with compatible first-y, first-t, and every
ordered second-yy weak L² derivative. With

    F=∫_K |g∘L_i|²,       M=∫_K |B_i(g∘L_i)|²,

the aggregate squared norms satisfy

    Σ_j ||gY_j||² ≤ 2CF+(3/4)C(F+M),
    Σ_j ||gT_j||² ≤ C(F+M)/64,
    Σ_j Σ_k ||hYY_jk||² ≤ (3/2)C(F+M).

The denominator 64 is exactly 16c with c=4. No additional coordinate or
spin-count factor is introduced. F and M are actual compact integrals; their
finiteness follows from the continuity/local L² input and the continuous
coefficient on K. C is an existence constant, not a computed rational
constant or a claimed complexity bound.

The scalar theorem explicitly takes a continuous representative of its graph
solution. It pulls back this actual function; it does not infer preservation
of arbitrary physical almost-everywhere identities under the dimension-changing
KS map. The spin theorem
`coulomb_spin_nuclear_KS_one_step_representative` constructs one representative
u for every spin component, using the earlier locally Lipschitz representative
theorem. It retains the pointwise simultaneous fermionic permutation law and
the previously proved spin-amplitude bound. For each i and χ, one K,C works
for every spin configuration σ; F,M and the derivative witnesses are then
component-specific.

The quantifier order is precise: the general potential wrapper fixes K,C
before B,f,g; the scalar application fixes them before f and g; the spin
statement fixes them before σ. The outer spin input ψ and its graph premise
occur earlier in that final theorem. This checkpoint does not present its
statement as a stronger outer ∃K,C∀ψ assertion. The proof obtains K,C from
the scalar geometry theorem before inspecting spin components.

The new gain is anisotropic. It gives first-y and first-t derivatives and the
full ordered yy Hessian of the localized KS pullback, including at the
selected nuclear collision. It does not yet assert mixed yt derivatives,
second-tt derivatives, full joint H², analytic estimates, factorial bounds,
an approximation algorithm, or full Theorem T. No spectral conclusion follows
from this regularity application alone.

The four immutable sources are `ProductContinuousLocalL2_v1.lean`,
`LocalWeakGrushinPotentialGain_v1.lean`, `CoulombNuclearKSOneStep_v1.lean`, and
`CoulombSpinNuclearKSOneStep_v1.lean`. Their existing successful compile and
strict expanded-statement/axiom receipts were checked against the final source
and object hashes. All four declarations have only propext, Classical.choice,
and Quot.sound. No repeat compiler or broad audit was needed. Pinned dependency
objects were reused in those builds; the four sources are outside the completed
671-target desktop source-rebuild snapshot.

Frozen historical reference: commit
`166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag
`theorem-t-proof-freeze-2026-09-09`,
`THEOREM_T_FREEZE_2026-09-09_212604/RWA_REPORT.md`, SHA-256
`2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`.
Frozen and successful source bytes and previous audit records are unchanged.
