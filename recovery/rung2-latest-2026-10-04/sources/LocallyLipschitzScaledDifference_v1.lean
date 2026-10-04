import ProductContinuousLocalL2_v1
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Actual origin-scaled differences. Bounds are uniform in the scale and
use only a local Lipschitz constant of the unscaled function. No derivative
at the origin is asserted. -/
noncomputable section
open Filter Metric
open scoped Topology NNReal
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def originScaledDifference (g : E → ℂ) (ε : ℝ) (x : E) : ℂ :=
  ε⁻¹ • (g (ε • x) - g 0)

theorem originScaledDifference_norm_le {g : E → ℂ} {L : ℝ≥0} {R ε : ℝ}
    (hR : 0 < R) (hg : LipschitzOnWith L g (ball 0 R)) (hε : 0 < ε)
    {x : E} (hx : ε * ‖x‖ < R) :
    ‖originScaledDifference g ε x‖ ≤ (L : ℝ) * ‖x‖ := by
  have hxball : ε • x ∈ ball (0 : E) R := by
    simpa only [mem_ball, dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos hε] using hx
  have hz : (0 : E) ∈ ball (0 : E) R := by simpa using hR
  have h := hg.dist_le_mul (ε • x) hxball 0 hz
  simp only [dist_eq_norm, sub_zero, norm_smul, Real.norm_eq_abs, abs_of_pos hε] at h
  calc
    ‖originScaledDifference g ε x‖ = ε⁻¹ * ‖g (ε • x) - g 0‖ := by
      simp only [originScaledDifference, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hε)]
    _ ≤ ε⁻¹ * ((L : ℝ) * (ε * ‖x‖)) := mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hε.le)
    _ = (L : ℝ) * ‖x‖ := by field_simp

theorem locallyLipschitz_origin_ball {g : E → ℂ} (hg : LocallyLipschitz g) :
    ∃ L : ℝ≥0, ∃ R : ℝ, 0 < R ∧ LipschitzOnWith L g (ball 0 R) := by
  obtain ⟨L,U,hU,hL⟩ := hg 0
  obtain ⟨R,hR,hRU⟩ := Metric.mem_nhds_iff.mp hU
  exact ⟨L,R,hR,hL.mono hRU⟩

theorem locallyLipschitz_scaled_difference_uniform {g : E → ℂ}
    (hg : LocallyLipschitz g) :
    ∃ L : ℝ≥0, ∃ R : ℝ, 0 < R ∧
      ∀ M : ℝ, 0 ≤ M → ∀ ε : ℝ, 0 < ε → ε ≤ R / (M + 1) →
        ∀ x : E, ‖x‖ ≤ M →
          ‖originScaledDifference g ε x‖ ≤ (L : ℝ) * M := by
  obtain ⟨L,R,hR,hL⟩ := locallyLipschitz_origin_ball hg
  refine ⟨L,R,hR,?_⟩
  intro M hM ε hε hεR x hx
  have hMR : ε * (M + 1) ≤ R := (le_div_iff₀ (by positivity)).mp hεR
  have hscaled : ε * ‖x‖ < R := by nlinarith
  exact (originScaledDifference_norm_le hR hL hε hscaled).trans
    (mul_le_mul_of_nonneg_left hx L.property)

theorem originScaledDifference_continuous {g : E → ℂ} (hg : Continuous g) (ε : ℝ) :
    Continuous (originScaledDifference g ε) := by
  exact ((hg.comp (continuous_const.smul continuous_id)).sub continuous_const).const_smul ε⁻¹

#print axioms originScaledDifference
#print axioms originScaledDifference_norm_le
#print axioms locallyLipschitz_origin_ball
#print axioms locallyLipschitz_scaled_difference_uniform
#print axioms originScaledDifference_continuous
end TheoremT.Continuum
