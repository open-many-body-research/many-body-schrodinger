import GenericWeakEllipticGain_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_real_test_integrable (f : Lp ℂ 2 (volume : Measure E)) {φ : E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x • f x) :=
  ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport
    hφ hc

theorem generic_integral_test_add (f g : Lp ℂ 2 (volume : Measure E)) {φ : E → ℝ}
    (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x • (f + g) x) = (∫ x, φ x • f x) + (∫ x, φ x • g x) := by
  calc
    _ = ∫ x, φ x • f x + φ x • g x := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_add f g] with x hx
      simp only [hx, Pi.add_apply, smul_add]
    _ = _ := integral_add (generic_real_test_integrable f hφ hc) (generic_real_test_integrable g hφ hc)

theorem generic_integral_test_smul (c : ℂ) (f : Lp ℂ 2 (volume : Measure E))
    (φ : E → ℝ) :
    (∫ x, φ x • (c • f) x) = c • (∫ x, φ x • f x) := by
  calc
    _ = ∫ x, c • (φ x • f x) := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f] with x hx
      rw [hx]
      exact smul_comm (φ x) c (f x)
    _ = _ := integral_smul c _

theorem weakL2Directional_zero (v : E) :
    WeakL2Directional (0 : Lp ℂ 2 (volume : Measure E)) 0 v := by
  intro φ hφ hc
  simp

theorem weakL2Directional_add {f g df dg : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hf : WeakL2Directional f df v) (hg : WeakL2Directional g dg v) :
    WeakL2Directional (f + g) (df + dg) v := by
  intro φ hφ hc
  have hdφ : Continuous (fun x => fderiv ℝ φ x v) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  rw [generic_integral_test_add df dg hφ.continuous hc,
    generic_integral_test_add f g hdφ (hc.fderiv_apply ℝ v), hf φ hφ hc, hg φ hφ hc]
  abel

theorem weakL2Directional_smul (c : ℂ) {f df : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hf : WeakL2Directional f df v) : WeakL2Directional (c • f) (c • df) v := by
  intro φ hφ hc
  rw [generic_integral_test_smul, generic_integral_test_smul, hf φ hφ hc, smul_neg]


#print axioms weakL2Directional_add
#print axioms weakL2Directional_smul
end TheoremT.Continuum
