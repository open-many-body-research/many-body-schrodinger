import HydrogenSphereC1Limit_v1
import PolarKineticSplit_v1
import SphericalVariance_v1

/-! Real and imaginary components of the actual complex sphere derivative and
area-normalized mean. No angular energy estimate is an assumption. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Polar
open TheoremT.HydrogenPolynomial

theorem fderiv_complex_re {f : AngularR3 → ℂ} (hf : Differentiable ℝ f)
    (x v : AngularR3) :
    fderiv ℝ (fun y => (f y).re) x v = (fderiv ℝ f x v).re := by
  have h := Complex.reCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  exact congrArg (fun L : AngularR3 →L[ℝ] ℝ => L v) h.fderiv

theorem fderiv_complex_im {f : AngularR3 → ℂ} (hf : Differentiable ℝ f)
    (x v : AngularR3) :
    fderiv ℝ (fun y => (f y).im) x v = (fderiv ℝ f x v).im := by
  have h := Complex.imCLM.hasFDerivAt.comp x (hf x).hasFDerivAt
  exact congrArg (fun L : AngularR3 →L[ℝ] ℝ => L v) h.fderiv

theorem tangential_complex_re {f : AngularR3 → ℂ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x : AngularR3) :
    tangentialPartial i (fun y => (f y).re) x = (complexTangentialPartial i f x).re := by
  simp only [tangentialPartial, euclideanPartial, complexTangentialPartial,
    fderiv_complex_re hf, Complex.sub_re, Complex.smul_re, smul_eq_mul]

theorem tangential_complex_im {f : AngularR3 → ℂ} (hf : Differentiable ℝ f)
    (i : Fin 3) (x : AngularR3) :
    tangentialPartial i (fun y => (f y).im) x = (complexTangentialPartial i f x).im := by
  simp only [tangentialPartial, euclideanPartial, complexTangentialPartial,
    fderiv_complex_im hf, Complex.sub_im, Complex.smul_im, smul_eq_mul]

theorem normalizedSphereMean_re {f : AngularR3 → ℂ} (hf : Continuous f) :
    (normalizedSphereMean (fun w => f w.val)).re = sphereMean (fun x => (f x).re) := by
  have hi : Integrable (fun w : Metric.sphere (0 : AngularR3) 1 => f w.val) sphereMeasure :=
    continuous_sphere_integrable (hf.comp continuous_subtype_val)
  simp only [normalizedSphereMean, sphereMean, Complex.smul_re, smul_eq_mul]
  have he := integral_re hi
  change (∫ w : Metric.sphere (0 : AngularR3) 1, (f w.val).re ∂sphereMeasure) =
    (∫ w : Metric.sphere (0 : AngularR3) 1, f w.val ∂sphereMeasure).re at he
  rw [← he]
  simp only [RCLike.re_to_complex, sphereMeasure, div_eq_mul_inv, mul_comm]

theorem normalizedSphereMean_im {f : AngularR3 → ℂ} (hf : Continuous f) :
    (normalizedSphereMean (fun w => f w.val)).im = sphereMean (fun x => (f x).im) := by
  have hi : Integrable (fun w : Metric.sphere (0 : AngularR3) 1 => f w.val) sphereMeasure :=
    continuous_sphere_integrable (hf.comp continuous_subtype_val)
  simp only [normalizedSphereMean, sphereMean, Complex.smul_im, smul_eq_mul]
  have he := integral_im hi
  change (∫ w : Metric.sphere (0 : AngularR3) 1, (f w.val).im ∂sphereMeasure) =
    (∫ w : Metric.sphere (0 : AngularR3) 1, f w.val ∂sphereMeasure).im at he
  rw [← he]
  simp only [RCLike.im_to_complex, sphereMeasure, div_eq_mul_inv, mul_comm]

theorem continuous_complexTangentialPartial {f : AngularR3 → ℂ}
    (hf : ContDiff ℝ 1 f) (i : Fin 3) : Continuous (complexTangentialPartial i f) := by
  have hd := hf.continuous_fderiv (by simp)
  exact (hd.clm_apply continuous_const).sub
    ((EuclideanSpace.proj i).continuous.smul (hd.clm_apply continuous_id))

theorem complex_norm_sq_components (z : ℂ) : ‖z‖^2 = z.re^2 + z.im^2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

end TheoremT.Polar
