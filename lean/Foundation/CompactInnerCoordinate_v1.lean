import CompactDirectionalGreen_v1

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_directional_inner_ibp {u w : E → F}
    (hu : ContDiff ℝ ∞ u) (hw : ContDiff ℝ ∞ w)
    (hc : HasCompactSupport u) (v : E) :
    (∫ x, inner ℝ (u x) (fderiv ℝ w x v) ∂μ) =
      -(∫ x, inner ℝ (fderiv ℝ u x v) (w x) ∂μ) := by
  have hdU : Continuous (fun x => fderiv ℝ u x v) :=
    (hu.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  have hdW : Continuous (fun x => fderiv ℝ w x v) :=
    (hw.continuous_fderiv_apply (by simp)).comp (continuous_id.prodMk continuous_const)
  exact integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := μ)
    (B := innerSL ℝ) (v := v)
    (compact_real_inner_integrable_general hdU hw.continuous (hc.fderiv_apply ℝ v))
    (compact_real_inner_integrable_general hu.continuous hdW hc)
    (compact_real_inner_integrable_general hu.continuous hw.continuous hc)
    (fun x _ => hu.differentiable (by simp) x)
    (fun x _ => hw.differentiable (by simp) x)

theorem compact_inner_coordinate_identity (L : E →L[ℝ] ℝ) (v : E)
    {u : E → F} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) :
    2*(∫ x, L x * inner ℝ (u x) (fderiv ℝ u x v) ∂μ) =
      -(L v)*(∫ x, ‖u x‖^2 ∂μ) := by
  let D : E → F := fun x => fderiv ℝ u x v
  have hD : Continuous D :=
    (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hI : Integrable (fun x => L x * inner ℝ (u x) (D x)) μ := by
    apply (L.continuous.mul (hu.continuous.inner (𝕜 := ℝ) hD)).integrable_of_hasCompactSupport
    apply hc.mono
    intro x hx
    change u x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hU : Integrable (fun x => ‖u x‖^2) μ := by
    simpa only [real_inner_self_eq_norm_sq] using
      compact_real_inner_integrable_general (μ := μ) hu.continuous hu.continuous hc
  let W : E → ℝ := fun x => L x * inner ℝ (u x) (u x)
  have hW : ContDiff ℝ 1 W := L.contDiff.mul (hu.inner (𝕜 := ℝ) hu)
  have hcW : HasCompactSupport W := by
    apply hc.mono
    intro x hx
    change u x ≠ 0
    intro hz
    exact hx (by simp [W,hz])
  have hd (x : E) : fderiv ℝ W x v = L v*‖u x‖^2+2*(L x*inner ℝ (u x) (D x)) := by
    have h := (hu.differentiable (by norm_num) x).hasFDerivAt
    have hh := (L.hasFDerivAt (x := x)).mul (h.inner (𝕜 := ℝ) h)
    change HasFDerivAt W _ x at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      smul_eq_mul,ContinuousLinearMap.comp_apply,ContinuousLinearMap.prod_apply,
      fderivInnerCLM_apply,real_inner_self_eq_norm_sq]
    simp only [D,real_inner_comm]
    ring
  have hz := compact_real_directional_integral_zero (μ := μ) hW hcW v
  simp_rw [hd] at hz
  have hUi : Integrable (fun x => L v*‖u x‖^2) μ := hU.const_mul _
  have hIi : Integrable (fun x => 2*(L x*inner ℝ (u x) (D x))) μ := hI.const_mul _
  rw [integral_add hUi hIi,integral_const_mul,integral_const_mul] at hz
  change 2*(∫ x,L x*inner ℝ (u x) (D x) ∂μ) = _
  linarith

#print axioms compact_directional_inner_ibp
#print axioms compact_inner_coordinate_identity
end TheoremT.Continuum
