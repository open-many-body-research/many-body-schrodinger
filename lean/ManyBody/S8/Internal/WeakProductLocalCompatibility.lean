import ManyBody.S8.Internal.HigherSpectatorRegularity
import CompactHessianCross_v1

/-!
# Genuine local compatibility of product weak derivatives

These test identities transport derivatives across plateau cutoffs and commute
actual mixed weak derivatives.  Neither classical differentiability of the weak
solution nor an assumed commutation equation is required.
-/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
open TheoremT.Continuum TheoremT.Continuum.WeakGrushin

namespace ManyBody.S8
variable {κ : Type} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem weak_product_mixed_commute
    {U dv dw e : Lp ℂ 2 (volume : Measure (Space κ))} {v w : Space κ}
    (hv : WeakProductL2Directional U dv v) (hw : WeakProductL2Directional U dw w)
    (he : WeakProductL2Directional dv e w) :
    WeakProductL2Directional dw e v := by
  intro φ hφ hcφ
  have hDv : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  have hDw : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p w) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  rw [he φ hφ hcφ, hv _ hDw (hcφ.fderiv_apply ℝ w), neg_neg,
    hw _ hDv (hcφ.fderiv_apply ℝ v), neg_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun p =>
    congrArg (fun r : ℝ => r • U p) (smooth_second_directional_commute hφ p w v)

omit [DecidableEq κ] in
theorem weak_product_local_cutoff
    {Ω : Set (Space κ)} {U d : Lp ℂ 2 (volume : Measure (Space κ))}
    {v : Space κ}
    (hD : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • d p) = -(∫ p, fderiv ℝ φ p v • U p))
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (_hcχ : HasCompactSupport χ)
    (hχΩ : tsupport χ ⊆ Ω)
    (hm : MemLp χ ⊤ volume)
    (hDm : MemLp (fun p => fderiv ℝ χ p v) ⊤ volume) :
    WeakProductL2Directional (productBoundedRealMul χ hm U)
      (productBoundedRealMul χ hm d +
        productBoundedRealMul (fun p => fderiv ℝ χ p v) hDm U) v := by
  intro φ hφ hcφ
  have hDχ : ContDiff ℝ ∞ (fun p => fderiv ℝ χ p v) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  have hint (f : Lp ℂ 2 (volume : Measure (Space κ)))
      {ψ : Space κ → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
      Integrable (fun p => ψ p • f p) :=
    ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hψ hcψ
  have h1 := hint d (hφ.mul hχ).continuous hcφ.mul_right
  have h2 := hint U (hφ.mul hDχ).continuous hcφ.mul_right
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  have h3 := hint U (hDφ.mul hχ).continuous (hcφ.fderiv_apply ℝ v).mul_right
  have hs : tsupport (fun p => φ p * χ p) ⊆ Ω := tsupport_mul_subset_right.trans hχΩ
  have hw := hD _ (hφ.mul hχ) hcφ.mul_right hs
  have hprod (p : Space κ) :
      fderiv ℝ (fun q => φ q * χ q) p v =
        φ p * fderiv ℝ χ p v + fderiv ℝ φ p v * χ p := by
    have hh := (hφ.differentiable (by simp) p).hasFDerivAt.mul
      (hχ.differentiable (by simp) p).hasFDerivAt
    change HasFDerivAt (𝕜 := ℝ) (fun q => φ q * χ q) _ p at hh
    rw [hh.fderiv]
    simp only [add_apply, smul_apply, smul_eq_mul]
    ring
  simp_rw [hprod, add_smul] at hw
  rw [integral_add h2 h3] at hw
  have hl :
      (∫ p, φ p • (productBoundedRealMul χ hm d +
        productBoundedRealMul (fun p => fderiv ℝ χ p v) hDm U) p) =
        (∫ p, (φ p * χ p) • d p) + ∫ p, (φ p * fderiv ℝ χ p v) • U p := by
    calc
      _ = ∫ p, (φ p * χ p) • d p + (φ p * fderiv ℝ χ p v) • U p := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_add (productBoundedRealMul χ hm d)
          (productBoundedRealMul (fun p => fderiv ℝ χ p v) hDm U),
          productBoundedRealMul_ae χ hm d,
          productBoundedRealMul_ae (fun p => fderiv ℝ χ p v) hDm U] with p hp hd hu
        rw [hp, Pi.add_apply, hd, hu, smul_add, mul_smul, mul_smul]
      _ = _ := integral_add h1 h2
  have hr :
      (∫ p, fderiv ℝ φ p v • productBoundedRealMul χ hm U p) =
        ∫ p, (fderiv ℝ φ p v * χ p) • U p := by
    apply integral_congr_ae
    filter_upwards [productBoundedRealMul_ae χ hm U] with p hp
    rw [hp, mul_smul]
  rw [hl, hr, hw]
  abel

/-- Actual local weak directional differentiation of raw representatives. -/
def ProductWeakDirectionalOn (f g : Space κ → ℂ) (v : Space κ)
    (Ω : Set (Space κ)) : Prop :=
  ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
    (∫ p, φ p • g p) = -(∫ p, fderiv ℝ φ p v • f p)

omit [DecidableEq κ] in
theorem weak_product_local_mixed_commute
    {Ω : Set (Space κ)} {U dv dw e : Space κ → ℂ} {v w : Space κ}
    (hv : ProductWeakDirectionalOn U dv v Ω) (hw : ProductWeakDirectionalOn U dw w Ω)
    (he : ProductWeakDirectionalOn dv e w Ω) :
    ProductWeakDirectionalOn dw e v Ω := by
  intro φ hφ hcφ hsφ
  have hDv : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  have hDw : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p w) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  rw [he φ hφ hcφ hsφ,
    hv _ hDw (hcφ.fderiv_apply ℝ w) ((tsupport_fderiv_apply_subset ℝ w).trans hsφ), neg_neg,
    hw _ hDv (hcφ.fderiv_apply ℝ v) ((tsupport_fderiv_apply_subset ℝ v).trans hsφ), neg_neg]
  apply integral_congr_ae
  exact Eventually.of_forall fun p =>
    congrArg (fun r : ℝ => r • U p) (smooth_second_directional_commute hφ p w v)

omit [DecidableEq κ] in
theorem weak_product_on_plateau
    {Ω : Set (Space κ)} {f : Space κ → ℂ}
    {U d : Lp ℂ 2 (volume : Measure (Space κ))} {v : Space κ}
    {η : Space κ → ℝ}
    (hU : U =ᵐ[volume] (fun p => η p • f p))
    (hη : ∀ p ∈ Ω, η p = 1)
    (hD : WeakProductL2Directional U d v) :
    ProductWeakDirectionalOn f (d : Space κ → ℂ) v Ω := by
  intro φ hφ hcφ hsφ
  rw [hD φ hφ hcφ]
  apply congrArg Neg.neg
  apply integral_congr_ae
  filter_upwards [hU] with p hp
  by_cases ht : p ∈ tsupport φ
  · rw [hp, hη p (hsφ ht), one_smul]
  · rw [fderiv_of_notMem_tsupport ℝ ht]
    simp only [zero_apply, zero_smul]

#print axioms weak_product_local_mixed_commute
#print axioms weak_product_on_plateau

#print axioms weak_product_mixed_commute
#print axioms weak_product_local_cutoff
end ManyBody.S8

