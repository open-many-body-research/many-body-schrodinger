import WeakGrushinCutoffNormPointwise_v1
import GrushinCutoffCoefficients_v1

/-! Actual cutoff coefficient bounds. The compact-cutoff constants depend only
on the cutoff and c, and are independent of input functions and weak jets. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem cutoffGradientWeight_eq_grushinCutoffWeight (c : ℝ) (χ : Space κ → ℝ) :
    cutoffGradientWeight c χ = grushinCutoffWeight c χ := rfl

theorem combinedCutoffScalar_continuous (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) : Continuous (combinedCutoffScalar c χ) := by
  have hD (v : Space κ) : ContDiff ℝ ∞ (fun p => fderiv ℝ χ p v) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hDD (v w : Space κ) : Continuous
      (fun p => fderiv ℝ (fun q => fderiv ℝ χ q v) p w) :=
    ((hD v).continuous_fderiv (by simp)).clm_apply continuous_const
  exact (continuous_finsetSum _ (fun i _ => hDD (yDir i) (yDir i))).add
    ((continuous_const.mul (continuous_fst.norm.pow 2)).mul
      (continuous_finsetSum _ (fun j _ => hDD (tDir j) (tDir j))))

theorem combinedCutoffScalar_zero_off_support
    (c : ℝ) (χ : Space κ → ℝ) {p : Space κ} (hp : p ∉ tsupport χ) :
    combinedCutoffScalar c χ p = 0 := by
  have hDD (v w : Space κ) : fderiv ℝ (fun q => fderiv ℝ χ q v) p w = 0 := by
    have hz : p ∉ tsupport (fun q => fderiv ℝ χ q v) :=
      fun hh => hp ((tsupport_fderiv_apply_subset ℝ v) hh)
    rw [fderiv_of_notMem_tsupport ℝ hz]
    rfl
  simp only [combinedCutoffScalar,hDD,Finset.sum_const_zero,mul_zero,add_zero]

theorem combinedCutoffScalar_exists_bound (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ p, |combinedCutoffScalar c χ p| ≤ A := by
  obtain ⟨A,hA⟩ := hcχ.exists_bound_of_continuousOn
    (combinedCutoffScalar_continuous c hχ).continuousOn
  refine ⟨max A 0,le_max_right _ _,fun p => ?_⟩
  by_cases hp : p ∈ tsupport χ
  · exact (hA p hp).trans (le_max_left _ _)
  · rw [combinedCutoffScalar_zero_off_support c χ hp,abs_zero]
    exact le_max_right _ _

theorem combinedCutoffScalar_explicit_bound {c : ℝ} (hc : 0 ≤ c)
    (A_Y A_T R : ℝ) (hAY : 0 ≤ A_Y) (hAT : 0 ≤ A_T) (χ : Space κ → ℝ)
    (hY : ∀ p, |∑ i : Fin 4, fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i)| ≤ A_Y)
    (hT : ∀ p, |∑ j : κ, fderiv ℝ (fun q => fderiv ℝ χ q (tDir j)) p (tDir j)| ≤ A_T)
    (hR : ∀ p ∈ tsupport χ, ‖p.1‖ ≤ R) :
    ∀ p, |combinedCutoffScalar c χ p| ≤ A_Y+c*R^2*A_T := by
  intro p
  by_cases hp : p ∈ tsupport χ
  · have hR2 := pow_le_pow_left₀ (norm_nonneg p.1) (hR p hp) 2
    have hw : 0 ≤ c*‖p.1‖^2 := mul_nonneg hc (sq_nonneg _)
    have hfirst := abs_add_le
      (∑ i : Fin 4, fderiv ℝ (fun q => fderiv ℝ χ q (yDir i)) p (yDir i))
      ((c*‖p.1‖^2)*(∑ j : κ, fderiv ℝ (fun q => fderiv ℝ χ q (tDir j)) p (tDir j)))
    have hnext := add_le_add (hY p) (mul_le_mul_of_nonneg_left (hT p) hw)
    have hlast := add_le_add_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hR2 hc) hAT) A_Y
    simp only [abs_mul,abs_of_nonneg hw] at hfirst
    exact hfirst.trans (hnext.trans hlast)
  · rw [combinedCutoffScalar_zero_off_support c χ hp,abs_zero]
    positivity

theorem weak_cutoff_coefficient_bounds (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧
      (∀ p, |combinedCutoffScalar c χ p| ≤ A) ∧
      (∀ p, cutoffGradientWeight c χ p ≤ B) := by
  obtain ⟨A,hA,ha⟩ := combinedCutoffScalar_exists_bound c hχ hcχ
  obtain ⟨B,hB,hb⟩ := grushinCutoffWeight_exists_bound c hχ hcχ
  exact ⟨A,B,hA,hB,ha,hb⟩

#print axioms combinedCutoffScalar_exists_bound
#print axioms combinedCutoffScalar_explicit_bound
#print axioms weak_cutoff_coefficient_bounds
end TheoremT.Continuum.WeakGrushin
