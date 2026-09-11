import WeakGrushinCutoffNormL2_v1
import CompactWeakGrushinOutputEstimates_v1

/-! Quantitative norm estimate for an explicitly identified L2 cutoff output.
The local weak PDE will discharge this AE formula premise in the next module. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem cutoff_output_norm_sq_le_of_ae {c : ℝ} (hc : 0 ≤ c)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (f h : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)))
    {K : Set (Space κ)} (hK : IsCompact K) (hs : tsupport χ ⊆ K)
    (M A B : ℝ) (hM : ∀ p, |χ p| ≤ M)
    (hA : ∀ p ∈ K, |combinedCutoffScalar c χ p| ≤ A)
    (hB : ∀ p ∈ K, cutoffGradientWeight c χ p ≤ B)
    (H : Lp ℂ 2 (volume : Measure (Space κ)))
    (hH : H =ᵐ[volume] (fun p => χ p • h p - combinedCutoffError c χ f d p)) :
    ‖H‖^2 ≤ 2*M^2*‖h‖^2 + 4*A^2*(∫ p in K, ‖f p‖^2) +
      16*B*firstJetEnergyOn c K d := by
  have ih := (Lp.memLp h).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have ie := (combinedCutoffError_memLp c hχ hcχ f d).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have iH := (Lp.memLp H).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have ir : Integrable (fun p => 2*M^2*‖h p‖^2 +
      2*‖combinedCutoffError c χ f d p‖^2) :=
    (ih.const_mul (2*M^2)).add (ie.const_mul 2)
  have ierr := combinedCutoffError_integral_norm_sq_le hc hχ hcχ f d hK hs A B hA hB
  calc
    ‖H‖^2 = ∫ p, ‖H p‖^2 := l2_norm_sq_integral H
    _ ≤ ∫ p, 2*M^2*‖h p‖^2 + 2*‖combinedCutoffError c χ f d p‖^2 := by
      apply integral_mono_ae iH ir
      filter_upwards [hH] with p hp
      rw [hp]
      have htri : ‖χ p • h p - combinedCutoffError c χ f d p‖^2 ≤
          2*(|χ p|^2*‖h p‖^2)+2*‖combinedCutoffError c χ f d p‖^2 := by
        simpa only [sub_eq_add_neg,norm_neg,norm_smul,Real.norm_eq_abs,mul_pow] using
          norm_add_sq_le_twice (χ p • h p) (-combinedCutoffError c χ f d p)
      have hsq := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (abs_nonneg _) (hM p) 2) (sq_nonneg ‖h p‖)
      nlinarith
    _ = 2*M^2*‖h‖^2 + 2*(∫ p, ‖combinedCutoffError c χ f d p‖^2) := by
      rw [integral_add (ih.const_mul (2*M^2)) (ie.const_mul 2),
        integral_const_mul,integral_const_mul,← l2_norm_sq_integral h]
    _ ≤ _ := by nlinarith

#print axioms cutoff_output_norm_sq_le_of_ae
end TheoremT.Continuum.WeakGrushin
