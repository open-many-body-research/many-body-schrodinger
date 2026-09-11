> **Archived research note (v1.0 foundation).** Written during AI-assisted exploratory work before publication. Labels such as "PROVEN", "independently reviewed" or "sealed" in this file are the original authors' and are **not** evidence tiers. The authoritative status of every claim is in [`claims/registry.yaml`](../../../../claims/registry.yaml) and [`STATUS.md`](../../../../STATUS.md). File paths refer to the private workspace layout.

# Partial tangential regularization: exact weak gain and its boundary

2026-09-10. Evidence category: **paper proof and targeted adversarial review**. No new Lean theorem is asserted here. This review concerns the passage from the now-compiled compact Grushin estimates to weak local estimates; it does not repeat the previously reviewed finite multi-index schedule or establish full Theorem T.

Reviewed inputs:

- `GRUSHIN_H12_WEAK_INITIALIZATION_v1.md`, SHA-256 `ba8d2c6a07c4c875f11402ca867ea52976911e29f4a93ab4bd8e8412fd503812`, especially H7–H12.
- `GRUSHIN_H12_ROOT_REVIEW_v1.md` (earlier paper review, not kernel verification).
- `../lean/CompactGrushinEstimates_v1.lean`, SHA-256 `f9a7bfd2765d13a39b8cde6f2b87218c79bd34c42025df5bb78475ded3f36e25`: actual smooth compact complex-valued functions on R⁴×Rᵐ, product Lebesgue measure, c≥0, with the three displayed quantitative estimates.

The inherited H12 argument's partial convolution is valid as written: it first sets h=f−Bv and convolves the equation P_cv=h. No error in that claim was established. Two tempting strengthenings are invalid and should be excluded explicitly in its formalization: multiplication by t-dependent B does not commute with partial convolution, and a single L² forcing step does not imply joint local H². The latter has an explicit compactly supported counterexample below. Neither strengthening is a claim of the inherited H9 statement, so this is not an erratum to H9.

## 1. Exact local lemma

Let m≥1, c>0 and P_c=−Δ_y−c|y|²Δ_t on R⁴×Rᵐ. Use the boxes Ω_j and positive gap δ of H1, with all norms below taken using product Lebesgue measure. Let R bound |y| on Ω_j. Choose real C² cutoffs η,χ satisfying 0≤η,χ≤1,

- η=1 on Ω_{j+1}, supp η⊂closure Ω_{j+1/2};
- χ=1 on Ω_{j+2}, supp χ⊂closure Ω_{j+3/2};
- |∇_yη|, |∇_tη|, |∇_yχ|, |∇_tχ|≤L₁;
- |Δ_yχ|, |Δ_tχ|≤L₂.

For v,h∈L²(Ω_j;C), suppose P_cv=h in distributions. Define W=||v||₂, H=||h||₂ and

    K = L₁ sqrt(1+cR²),
    E = sqrt(1+4K²),
    J = 1 + 2L₁(1+sqrt(c)R)E + L₂(1+cR²),
    G = 1 + E + ((4sqrt(c))⁻¹ + sqrt(3/2))J.

Then v has actual weak first derivatives in y and t and actual weak ordered second derivatives in y on Ω_{j+2}, with

    max{||v||₂, ||∇_y v||₂, ||∇_t v||₂, ||D_y² v||₂}
      ≤ G(W+H).                                           (A)

The Hessian norm sums the squares of all 16 ordered y derivatives. A proof must separately supply the ordinary Fourier identity ||D_y²z||₂=||Δ_yz||₂. The current compact Lean theorem directly bounds Δ_y; that identity and the passage to compact H² cannot be omitted from the formal dependency graph.

For Q=P_c+B, B merely measurable and essentially bounded with ||B||∞≤b₀, the same conclusion for Qv=f follows with h=f−Bv and constant (1+b₀)G multiplying W+||f||₂. No smallness, analyticity or derivatives of B are required for this single step. The hypothesis c>0 is essential for an unweighted tangential gain; the current compact theorem permits c=0, but its tangential conclusion then becomes 0≤||P_0z||².

## 2. Regularization with its true right side

Extend v,h by zero only in t, retaining y in the original open y-box. For a nonnegative C∞ compactly supported kernel ρ_μ on Rᵐ with integral one and support in a ball of radius μ<δ/4, put

    v_μ(y,t) = ∫ρ_μ(s)v(y,t−s)ds,
    h_μ(y,t) = ∫ρ_μ(s)h(y,t−s)ds.

The interior equation is exactly P_cv_μ=h_μ on Ω_{j+1/4}. To verify it distributionally, move convolution onto a compactly supported test function by Fubini. Its translates remain within Ω_j. All coefficients of P_c are independent of t, so the shifted test function has the identical y coefficient. No derivative of the zero extension is taken at its boundary.

Young's inequality gives the uniform bounds

    ||v_μ||_{L²(Y_j×Rᵐ)}≤W,  ||h_μ||_{L²(Y_j×Rᵐ)}≤H.

For each fixed μ, every t derivative of v_μ and h_μ is locally L², since it equals convolution with the corresponding derivative of ρ_μ. Those derivative bounds may grow like negative powers of μ; none may occur in the final uniform estimate.

For Qv=f, the true equation is

    P_cv_μ = f_μ − (Bv)_μ,

and generally **not** (P_c+B)v_μ=f_μ. For example, locally in one t coordinate choose B(t)=t, v(t)=t and f(t)=t². Then P_cv=0. For a symmetric probability kernel with positive second moment σ_μ², v_μ=t but (Bv)_μ=f_μ=t²+σ_μ², whereas Bv_μ=t². Forming h=f−Bv before convolution removes this commutator exactly and preserves the bound H≤||f||₂+b₀W. No commutator convergence theorem or coefficient Lipschitz constant is needed.

This same order of operations applies after each finite tangential differentiation: first prove the distributional equation for the unmollified weak derivative w, including the genuine Leibniz terms; then set its full L² forcing h_w and regularize P_cw=h_w. Smoothing h_w supplies all preliminary t derivatives without assuming B has infinitely many derivatives.

## 3. Preliminary joint H² is legitimate for each fixed μ

In the interior distributional sense,

    Δ_{y,t}v_μ = (1−c|y|²)Δ_tv_μ − h_μ.                  (B)

The right side is locally L²: y is locally bounded and Δ_tv_μ is L² for fixed μ. Therefore the ordinary constant-coefficient local Laplacian theorem gives v_μ∈H²_loc in all 4+m variables. This theorem is independent of Grushin regularity. A self-contained construction is to convolve a distributional solution Δw=k in all variables, obtain a uniform H¹ interior bound by a cutoff energy estimate, apply the Fourier Hessian identity to a second cutoff, and pass to weak limits. This is the same ordinary elliptic argument used in H8, now in dimension 4+m.

Alternatively, use H8 with t as a Hilbert-space parameter: first apply it to v_μ, then to each ∂_{t_a}v_μ with the differentiated L² forcing. That gives all required mixed derivatives, while pure t derivatives already exist. Either approach is noncircular. The first route requires a genuinely generic finite-dimensional Laplacian lemma; a Lean theorem stated only for configuration dimension 3N does not instantiate directly at the KS dimension 3N+1.

There is enough margin: the fixed supports of η and χ lie compactly within Ω_{j+1/4}. Additional very small cutoffs needed in the preliminary elliptic argument cost only nonuniform μ-dependent bounds. They do not consume extra gaps from the eventual 34-gap schedule, because these bounds justify operations only; the final numerical estimate below is obtained on the predetermined η,χ.

## 4. Uniform energy and compact estimates

Testing P_cv_μ=h_μ with η² overline(v_μ), taking real parts and applying Cauchy–Schwarz gives, with

    X² = ||η∇_y v_μ||² + c||η|y|∇_t v_μ||²,

    X² ≤ HW + 2K W X
       ≤ (H²+W²)/2 + X²/2 + 2K²W².

Consequently

    X² ≤ H² + (1+4K²)W² ≤ E²(W+H)².                  (C)

The weak integration is justified by the preliminary local H² and approximation of η²v_μ by admissible compact test functions. The coefficient c|y|² is bounded on these supports. Complex h or B causes no change because only the real part of the sesquilinear pairing is used.

The exact commutator is

    [P_c,χ]u = −2∇_yχ·∇_yu − (Δ_yχ)u
                −2c|y|²∇_tχ·∇_tu − c|y|²(Δ_tχ)u.

Its derivatives of u are supported where η=1. The two first-order terms have combined norm at most 2L₁(1+sqrt(c)R)E(W+H); the zeroth-order terms have norm at most L₂(1+cR²)W. Thus

    ||P_c(χv_μ)||₂ ≤ J(W+H).                          (D)

Here χv_μ, extended by zero, is an actual compactly supported joint H² function. Approximate it in global H² by compact C∞ functions supported in one fixed larger box. Since |y|² is bounded on that containing box, P_cz_n→P_c(χv_μ) in L². This extends the proved compact estimates by ordinary H² density; it is not a claim that arbitrary graph-domain functions are H². Apply the compact estimates and the Fourier Hessian identity to obtain

    ||∇_t(χv_μ)||₂ ≤ J(W+H)/(4sqrt(c)),
    ||D_y²(χv_μ)||₂ ≤ sqrt(3/2)J(W+H).

Together with (C), these are uniform in μ. Partial convolution converges to v locally in L². Weak compactness in the finite product of derivative L² spaces supplies a subsequence; distributional convergence identifies every limit with its stated weak derivative of the original v. Restriction to Ω_{j+2} proves (A). No preliminary μ-dependent H² estimate survives into the bound.

A useful optional improvement follows from the exact localization identity now being formalized:

    ||∇_y(ηu)||²+c|||y|∇_t(ηu)||²
      = Re∫h η² overline(u)
          +∫(|∇_yη|²+c|y|²|∇_tη|²)|u|².

It bounds the gradient on the region where η=1 with E♯=sqrt(1+K²). Applying one Cauchy–Schwarz inequality to the combined y/t commutator gives J♯=1+2K E♯+L₂(1+cR²). The same formula for G with E♯,J♯ is valid. This changes no inherited claim; the larger original E,J are already correct and sufficient.

## 5. Explicit obstruction to a one-step joint H² conclusion

Set c=1, m=1. On R⁴×(−π,π), consider the L² series

    u(y,t)=Σ_{n≥1} n⁻¹ exp(−n|y|²/2) exp(int).

The t modes are orthogonal and ∫_{R⁴}exp(−n|y|²)dy=π²/n². Thus

    ||u||² = 2π³ Σ n⁻⁴ < ∞.

Each summand satisfies P_1(exp(−n|y|²/2)exp(int))=4n exp(−n|y|²/2)exp(int), so partial sums have L²-convergent images

    h=4Σ_{n≥1}exp(−n|y|²/2)exp(int),
    ||h||² = 32π³ Σ n⁻² < ∞.

Convergence in L² implies convergence in distributions, and P_1 acts continuously on distributions when paired with compact tests. Therefore P_1u=h distributionally, with no extra distribution concentrated at y=t=0.

For |y|>0, put z=exp(−|y|²/2+it). Absolute convergence gives

    u=−log(1−z),   ∂_t²u=−z/(1−z)².

On the region 0<r=|y|<min(1,ε), |t|≤r²/2,

    |z|≥exp(−1/2),   |1−z|≤r²/2+|t|≤r².

Hence |∂_t²u|²≥exp(−1)r⁻⁸. Integrating over this region, whose t length is r² and whose y radial volume is 2π²r³dr, gives a lower bound proportional to ∫₀^ε r⁻³dr=∞. It lies in any sufficiently small neighborhood of the origin. Thus u is not H²_loc there.

This example can be made compactly supported. Its first derivatives are L²: the orthogonal-mode sums give

    ||∂_t u||²=2π³Σ n⁻²,
    ||∂_{y_i}u||²=π³Σ n⁻³.

Choose a smooth cutoff ζ compactly supported in a small y/t box and equal to one near the origin. Then w=ζu lies in H¹ with compact support. The exact first-order commutator shows P_1w=ζh+[P_1,ζ]u∈L², since all coefficients on supp ζ are bounded and u has L² first derivatives. Nevertheless w is not H²_loc at the origin. Extra spectator coordinates may be added by taking u independent of them on a product box and then inserting cutoffs; the same obstruction holds for m=3 and higher.

The counterexample does not meet the stronger H11 forcing hypothesis needed by the finite initialization theorem. It invalidates only the stronger, unasserted inference “L² solution plus L² Grushin forcing implies joint H² in one step.” In the intended program, one first obtains (A), differentiates in t with sufficient source/coefficient regularity, repeats the gain, and then performs ordinary y recovery. That route is consistent with this obstruction.

## 6. Constants for more spectators and remaining formal dependencies

For m=3 the inherited L₁=24/δ and L₂=1200/δ² are valid. In arbitrary spectator dimension one may use

    L₁ = 8 max(2,sqrt(m))/δ,
    L₂ = 152 max(4,m)/δ²,

from the same tensor cutoff. The 34-gap H12 schedule still applies at fixed derivative order, but the y-recovery constant 3c(R²+20R+90) must become m c(R²+20R+90), and the number of total derivatives is binom(m+16,m+4). Keeping the number 3 or the count 50388 for arbitrary m would hide dimension dependence. The compact tangential factor 4sqrt(c) itself is independent of m because the y dimension remains four.

Exact next formal dependencies, without claiming them complete:

1. Generic finite-dimensional local Δ-to-H² regularity or the Hilbert-valued y-only version, independent of Grushin estimates.
2. Partial convolution of actual L² functions on product boxes, exact interior commutation, contraction, local convergence, and all fixed-radius t derivative representatives.
3. Weak integration by parts/localization for compact H² products, with the actual product volume.
4. Compact H² extension of the three model estimates and the full ordered y-Hessian Fourier identity.
5. Weak compactness plus distributional identification giving (A) for the original L² solution.
6. Finite Sobolev Leibniz rules and the already specified acyclic tangential/y derivative schedule.

These are analytic/formalization obligations, not obstacles remedied by faster hardware. The new compiled compact estimates discharge an important input to them, but neither this paper review nor the previous schedule checker supplies their Lean proofs.

Frozen provenance: `THEOREM_T_FREEZE_2026-09-09_212604/`, commit `166f43f2f0178f92d8c4d1dde209ef0eeaefa660`, tag `theorem-t-proof-freeze-2026-09-09`. Frozen `rwa_proof/UNIFORM_ANALYTIC_AUDIT.md` SHA-256 `5d83e7f2efe9a479f4cf53debc5c94d4653d87505489876151294487d93efe1c`; frozen `RWA_REPORT.md` SHA-256 `2545ac53ff24f8bebd0c25b1f09f6ced6b4d8b7bb49eef99cbc44eb9e2862066`. No frozen or previously sealed file was changed. No external literature result is required for the elementary arguments in this note, and no novelty claim is made.
