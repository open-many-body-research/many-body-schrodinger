import PartialFourierMixedPlancherel_v1
import PartialFourierLinear_v1

noncomputable section
open MeasureTheory
open scoped ContDiff FourierTransform
namespace TheoremT.Continuum
variable {Y T : Type} [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [MeasurableSpace T] [BorelSpace T] [FiniteDimensional ℝ T]

def yWeighted (w : Y → ℝ) (G : Y × T → ℂ) (p : Y × T) : ℂ := (w p.1 : ℂ)*G p

theorem yWeighted_continuous {w : Y → ℝ} (hw : Continuous w) {G : Y × T → ℂ}
    (hG : Continuous G) : Continuous (yWeighted w G) :=
  (Complex.continuous_ofReal.comp (hw.comp continuous_fst)).mul hG

theorem yWeighted_hasCompactSupport (w : Y → ℝ) {G : Y × T → ℂ}
    (hc : HasCompactSupport G) : HasCompactSupport (yWeighted w G) := hc.mul_left

theorem yWeighted_slice_contDiff (w : Y → ℝ) {G : Y × T → ℂ}
    (hG : ContDiff ℝ ∞ G) (y : Y) : ContDiff ℝ ∞ (fun t => yWeighted w G (y,t)) :=
  (contDiff_const (c := (w y : ℂ))).mul (compact_slice_contDiff hG y)

theorem yWeighted_norm_sq (w : Y → ℝ) (G : Y × T → ℂ) (p : Y × T) :
    ‖yWeighted w G p‖^2 = (w p.1)^2*‖G p‖^2 := by
  simp only [yWeighted,norm_mul,Complex.norm_real,mul_pow,Real.norm_eq_abs,sq_abs]

theorem partialFourier_yWeighted_norm_sq (w : Y → ℝ) (G : Y × T → ℂ) (ξ : T) (y : Y) :
    ‖partialFourier (yWeighted w G) ξ y‖^2 = (w y)^2*‖partialFourier G ξ y‖^2 := by
  have he : partialFourier (yWeighted w G) ξ y = (w y : ℂ)*partialFourier G ξ y :=
    partialFourier_y_mul (fun y => (w y : ℂ)) G ξ y
  rw [he]
  simp only [norm_mul,Complex.norm_real,mul_pow,Real.norm_eq_abs,sq_abs]

theorem partialFourier_weighted_plancherel {w : Y → ℝ} (hw : Continuous w)
    {G : Y × T → ℂ} (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G) :
    Integrable (fun ξ => ∫ y,(w y)^2*‖partialFourier G ξ y‖^2) volume ∧
      (∫ ξ, ∫ y,(w y)^2*‖partialFourier G ξ y‖^2) =
        ∫ p,(w p.1)^2*‖G p‖^2 ∂((volume : Measure Y).prod (volume : Measure T)) := by
  have hM := yWeighted_continuous hw hG.continuous
  have hcM := yWeighted_hasCompactSupport w hc
  have hsM := yWeighted_slice_contDiff w hG
  have hi := (partialFourier_joint_norm_sq_integrable_mixed hM hcM hsM).integral_prod_right
  have he := partialFourier_plancherel_product_mixed hM hcM hsM
  constructor
  · simpa only [partialFourier_yWeighted_norm_sq] using hi
  · simpa only [partialFourier_yWeighted_norm_sq,yWeighted_norm_sq] using he

#print axioms partialFourier_weighted_plancherel
end TheoremT.Continuum
