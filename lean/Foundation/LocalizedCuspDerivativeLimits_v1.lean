import SmoothLocalizedExponential_v1
import CoulombCuspDerivativeLimits_v1
import CoulombCuspExponentialBounds_v1

noncomputable section
open Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

def localizedCusp (N : ℕ) (Z : ℝ) (χ : Configuration N → ℝ) (x : Configuration N) : ℝ :=
  χ x*Real.exp (-coulombCusp N Z x)

def localizedCuspGradient (N : ℕ) (Z : ℝ) (χ : Configuration N → ℝ)
    (v x : Configuration N) : ℝ :=
  Real.exp (-coulombCusp N Z x)*(fderiv ℝ χ x v-χ x*coulombCuspGradient N Z v x)

def localizedCuspHessian (N : ℕ) (Z : ℝ) (χ : Configuration N → ℝ)
    (v w x : Configuration N) : ℝ :=
  Real.exp (-coulombCusp N Z x)*(fderiv ℝ (fun y => fderiv ℝ χ y v) x w-
    fderiv ℝ χ x v*coulombCuspGradient N Z w x-fderiv ℝ χ x w*coulombCuspGradient N Z v x+
    χ x*(coulombCuspGradient N Z v x*coulombCuspGradient N Z w x-coulombCuspHessian N Z v w x))

theorem localizedCusp_value_tendsto (N : ℕ) (Z : ℝ) (χ : Configuration N → ℝ)
    (x : Configuration N) :
    Tendsto (fun n => χ x*Real.exp (-regularizedCoulombCusp N Z (radiusRegularization n) x)) atTop
      (𝓝 (localizedCusp N Z χ x)) :=
  (regularized_cusp_exp_neg_tendsto N Z x).const_mul (χ x)

theorem localizedCusp_gradient_tendsto (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {x : Configuration N} (hx : collisionFree x) (v : Configuration N) :
    Tendsto (fun n => fderiv ℝ
      (fun y => χ y*Real.exp (-regularizedCoulombCusp N Z (radiusRegularization n) y)) x v) atTop
      (𝓝 (localizedCuspGradient N Z χ v x)) := by
  simp_rw [smooth_localized_exp_partial hχ (regularizedCoulombCusp_contDiff N Z (radiusRegularization_pos _))]
  exact (regularized_cusp_exp_neg_tendsto N Z x).mul
    (tendsto_const_nhds.sub (tendsto_const_nhds.mul (regularizedCoulombCusp_partial_tendsto N Z
      radiusRegularization_pos radiusRegularization_tendsto hx v)))

theorem localizedCusp_hessian_tendsto (N : ℕ) (Z : ℝ)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ)
    {x : Configuration N} (hx : collisionFree x) (v w : Configuration N) :
    Tendsto (fun n => fderiv ℝ (fun y => fderiv ℝ
      (fun z => χ z*Real.exp (-regularizedCoulombCusp N Z (radiusRegularization n) z)) y v) x w) atTop
      (𝓝 (localizedCuspHessian N Z χ v w x)) := by
  simp_rw [smooth_localized_exp_mixed hχ (regularizedCoulombCusp_contDiff N Z (radiusRegularization_pos _))]
  have hv := regularizedCoulombCusp_partial_tendsto N Z radiusRegularization_pos radiusRegularization_tendsto hx v
  have hw := regularizedCoulombCusp_partial_tendsto N Z radiusRegularization_pos radiusRegularization_tendsto hx w
  have hvw := regularizedCoulombCusp_hessian_tendsto N Z radiusRegularization_pos radiusRegularization_tendsto hx v w
  exact (regularized_cusp_exp_neg_tendsto N Z x).mul
    (((tendsto_const_nhds.sub (tendsto_const_nhds.mul hw)).sub (tendsto_const_nhds.mul hv)).add
      (tendsto_const_nhds.mul ((hv.mul hw).sub hvw)))

#print axioms localizedCusp_hessian_tendsto
end TheoremT.Continuum
