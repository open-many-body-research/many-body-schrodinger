import CompactInnerCoordinate_v1

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_weighted_directional_green (L : E →L[ℝ] ℝ) (v : E)
    {u : E → F} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    (∫ x, inner ℝ (-(fderiv ℝ (fun y => fderiv ℝ u y v) x v)) ((L x)^2 • u x) ∂μ) =
      (∫ x, (L x)^2*‖fderiv ℝ u x v‖^2 ∂μ)-(L v)^2*(∫ x, ‖u x‖^2 ∂μ) := by
  let D : E → F := fun x => fderiv ℝ u x v
  let W : E → F := fun x => (L x)^2 • u x
  have hD : ContDiff ℝ ∞ D :=
    (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hW : ContDiff ℝ ∞ W := (L.contDiff.pow 2).smul hu
  have hcW : HasCompactSupport W := by
    apply hc.mono
    intro x hx
    change u x ≠ 0
    intro hz
    exact hx (by simp [W,hz])
  have hder (x : E) : fderiv ℝ W x v = (2*L x*L v) • u x+(L x)^2 • D x := by
    have hh := ((L.hasFDerivAt (x := x)).pow 2).smul
      ((hu.differentiable (by simp) x).hasFDerivAt)
    change HasFDerivAt W _ x at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply,smul_eq_mul,Nat.reduceSub,pow_one,
      nsmul_eq_mul,Nat.cast_ofNat,D]
    exact add_comm _ _
  have hi := compact_directional_inner_ibp (μ := μ) hW hD hcW v
  have hleft : (fun x => inner ℝ (-(fderiv ℝ D x v)) ((L x)^2 • u x)) =
      (fun x => -(inner ℝ (W x) (fderiv ℝ D x v))) := by
    funext x
    simp only [inner_neg_left,real_inner_comm,W]
  have hright : (fun x => inner ℝ (fderiv ℝ W x v) (D x)) =
      (fun x => (L x)^2*‖D x‖^2+(2*L v)*(L x*inner ℝ (u x) (D x))) := by
    funext x
    rw [hder]
    simp only [inner_add_left,real_inner_smul_left,real_inner_self_eq_norm_sq]
    ring
  have hK : Integrable (fun x => (L x)^2*‖D x‖^2) μ := by
    apply ((L.continuous.pow 2).mul (hD.continuous.norm.pow 2)).integrable_of_hasCompactSupport
    apply (hc.fderiv_apply ℝ v).mono
    intro x hx
    change D x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hC : Integrable (fun x => L x*inner ℝ (u x) (D x)) μ := by
    apply (L.continuous.mul (hu.continuous.inner (𝕜 := ℝ) hD.continuous)).integrable_of_hasCompactSupport
    apply hc.mono
    intro x hx
    change u x ≠ 0
    intro hz
    exact hx (by simp [hz])
  have hCa : Integrable (fun x => (2*L v)*(L x*inner ℝ (u x) (D x))) μ := hC.const_mul _
  change (∫ x, inner ℝ (-(fderiv ℝ D x v)) ((L x)^2 • u x) ∂μ) = _
  rw [hleft,integral_neg,hi,neg_neg,hright,integral_add hK hCa,integral_const_mul]
  have hz := compact_inner_coordinate_identity (μ := μ) L v (hu.of_le (by simp)) hc
  change 2*(∫ x,L x*inner ℝ (u x) (D x) ∂μ) = _ at hz
  change (∫ x,(L x)^2*‖D x‖^2 ∂μ)+_ = (∫ x,(L x)^2*‖D x‖^2 ∂μ)-_
  nlinarith [congrArg (fun t : ℝ => L v*t) hz]

#print axioms compact_weighted_directional_green
end TheoremT.Continuum
