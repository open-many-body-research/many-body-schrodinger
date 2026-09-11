import HalfLineCoreDensity_v1
import HalfLineCompactPairing_v1

/-! The compact Hardy multiplier extends continuously to the entire declared
half-line domain. Identification with the actual quotient is proved separately. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine
open HalfLineCompactHardy

def quotientTestMap : Test →ₗ[ℂ] E where
  toFun f := f.quotientLp
  map_add' f g := by
    apply Lp.ext
    filter_upwards [(f+g).coe_quotientLp, f.coe_quotientLp, g.coe_quotientLp,
      Lp.coeFn_add f.quotientLp g.quotientLp] with x hfg hf hg ha
    simp only [Pi.add_apply] at ha
    rw [hfg, ha, hf, hg]
    simp [quotient, smul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [(c • f).coe_quotientLp, f.coe_quotientLp,
      Lp.coeFn_smul c f.quotientLp] with x hcf hf hc
    simp only [Pi.smul_apply] at hc
    change ((c • f).quotientLp : ℝ → ℂ) x = ((c • f.quotientLp : E) : ℝ → ℂ) x
    rw [hcf, hc, hf]
    exact smul_comm (x⁻¹ : ℝ) c (f x)

theorem quotientTestMap_bound (f : Test) : ‖quotientTestMap f‖ ≤ 2 * ‖testEmbed f‖ := by
  exact f.quotient_bound.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))

def W : D →L[ℂ] E := quotientTestMap.extendOfNorm testEmbed

theorem W_testEmbed (f : Test) : W (testEmbed f) = f.quotientLp :=
  LinearMap.extendOfNorm_eq testEmbed_dense ⟨2,quotientTestMap_bound⟩ f

theorem hardy_domain (u : D) : ‖W u‖ ≤ 2 * ‖dJ u‖ := by
  refine testEmbed_dense.induction_on (p := fun v => ‖W v‖ ≤ 2 * ‖dJ v‖) u ?_ ?_
  · exact isClosed_le (W.continuous.norm) (continuous_const.mul dJ.continuous.norm)
  · intro f
    rw [W_testEmbed, dJ_testEmbed]
    exact f.quotient_bound

theorem W_bound (u : D) : ‖W u‖ ≤ 2 * ‖u‖ :=
  LinearMap.norm_extendOfNorm_apply_le testEmbed_dense 2 quotientTestMap_bound u

#print axioms quotientTestMap
#print axioms W_testEmbed
#print axioms hardy_domain
#print axioms W_bound
end TheoremT.HalfLine
