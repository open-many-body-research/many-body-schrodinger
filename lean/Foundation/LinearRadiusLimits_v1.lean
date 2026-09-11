import RegularizedLinearRadiusBounds_v1

noncomputable section
open Filter
open scoped Topology
namespace TheoremT.Continuum

def linearRadiusHessian {N : ℕ} (A : Configuration N →L[ℝ] Position)
    (v w x : Configuration N) : ℝ :=
  inner ℝ (A w) (A v)/‖A x‖-inner ℝ (A x) (A v)*inner ℝ (A x) (A w)/‖A x‖^3

theorem regularizedLinearRadius_tendsto {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (x : Configuration N) :
    Tendsto (fun n => regularizedLinearRadius A (δ n) x) atTop (𝓝 ‖A x‖) := by
  convert! (hδ.const_add (‖A x‖^2)).sqrt using 1
  simp [Real.sqrt_sq (norm_nonneg (A x))]

theorem regularizedLinearRadius_partial_tendsto {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℕ → ℝ} (hp : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration N} (hx : A x ≠ 0) (v : Configuration N) :
    Tendsto (fun n => fderiv ℝ (regularizedLinearRadius A (δ n)) x v) atTop
      (𝓝 (inner ℝ (A x) (A v)/‖A x‖)) := by
  simp_rw [regularizedLinearRadius_fderiv_apply A (hp _)]
  exact tendsto_const_nhds.div (regularizedLinearRadius_tendsto A hδ x) (norm_ne_zero_iff.mpr hx)

theorem regularizedLinearRadius_hessian_tendsto {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {δ : ℕ → ℝ} (hp : ∀ n, 0 < δ n) (hδ : Tendsto δ atTop (𝓝 0))
    {x : Configuration N} (hx : A x ≠ 0) (v w : Configuration N) :
    Tendsto (fun n => fderiv ℝ (fun y => fderiv ℝ (regularizedLinearRadius A (δ n)) y v) x w)
      atTop (𝓝 (linearRadiusHessian A v w x)) := by
  simp_rw [regularizedLinearRadius_mixed_partial A (hp _)]
  have ht := regularizedLinearRadius_tendsto A hδ x
  exact (tendsto_const_nhds.div ht (norm_ne_zero_iff.mpr hx)).sub
    (tendsto_const_nhds.div (ht.pow 3) (pow_ne_zero _ (norm_ne_zero_iff.mpr hx)))

theorem linearRadiusHessian_bound {N : ℕ} (A : Configuration N →L[ℝ] Position)
    {x : Configuration N} (hx : A x ≠ 0) (v w : Configuration N) :
    ‖linearRadiusHessian A v w x‖ ≤ 2*‖A v‖*‖A w‖/‖A x‖ := by
  apply le_of_tendsto ((regularizedLinearRadius_hessian_tendsto A radiusRegularization_pos
    radiusRegularization_tendsto hx v w).norm)
  exact Eventually.of_forall (fun n => by
    simpa only [Real.norm_eq_abs] using
      regularizedLinearRadius_mixed_coulomb_bound A (radiusRegularization_pos n) hx v w)

#print axioms linearRadiusHessian_bound
end TheoremT.Continuum
