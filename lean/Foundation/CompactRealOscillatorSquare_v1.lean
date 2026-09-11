import CompactRealDirectionalIntegral_v1

/-! An exact completing-square identity, with the coordinate functional and its
normalization explicit. The derivatives and integrals are the actual ones. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_real_square_integrable_general {u : E → ℝ}
    (hu : Continuous u) (hc : HasCompactSupport u) :
    Integrable (fun x => (u x)^2) μ := by
  apply (hu.pow 2).integrable_of_hasCompactSupport
  simpa only [sq] using hc.mul_right (f' := u)

theorem compact_real_oscillator_square (L : E →L[ℝ] ℝ) (v : E) (hLv : L v=1)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (a : ℝ) :
    (∫ x, (fderiv ℝ u x v+a*L x*u x)^2 ∂μ) =
      (∫ x, (fderiv ℝ u x v)^2 ∂μ)+a^2*(∫ x, (L x*u x)^2 ∂μ)-a*(∫ x, (u x)^2 ∂μ) := by
  let D : E → ℝ := fun x => fderiv ℝ u x v
  have hD : Continuous D :=
    (hu.continuous_fderiv_apply (by norm_num)).comp (continuous_id.prodMk continuous_const)
  have hcD : HasCompactSupport D := hc.fderiv_apply ℝ v
  have hDu : Integrable (fun x => (D x)^2) μ := compact_real_square_integrable_general hD hcD
  have hLu : Integrable (fun x => (L x*u x)^2) μ :=
    compact_real_square_integrable_general (L.continuous.mul hu.continuous) hc.mul_left
  have hU : Integrable (fun x => (u x)^2) μ := compact_real_square_integrable_general hu.continuous hc
  have hC : Integrable (fun x => L x*u x*D x) μ :=
    ((L.continuous.mul hu.continuous).mul hD).integrable_of_hasCompactSupport hc.mul_left.mul_right
  let W : E → ℝ := fun x => (u x)^2*L x
  have hW : ContDiff ℝ 1 W := (hu.pow 2).mul L.contDiff
  have hcW : HasCompactSupport W := by
    apply hc.mono
    intro x hx
    change u x ≠ 0
    intro hz
    apply hx
    simp [W,hz]
  have hder (x : E) : fderiv ℝ W x v=2*(L x*u x*D x)+(u x)^2 := by
    have hd := (hu.differentiable (by norm_num) x).hasFDerivAt
    have hh := (hd.pow 2).mul (L.hasFDerivAt (x := x))
    change HasFDerivAt W _ x at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul,
      Nat.cast_ofNat,pow_one,hLv,D]
    ring
  have hz := compact_real_directional_integral_zero (μ := μ) hW hcW v
  simp_rw [hder] at hz
  have hC2 : Integrable (fun x => 2*(L x*u x*D x)) μ := hC.const_mul 2
  rw [integral_add hC2 hU,integral_const_mul] at hz
  have he : (fun x => (fderiv ℝ u x v+a*L x*u x)^2)=
      fun x => ((D x)^2+a^2*(L x*u x)^2)+(2*a)*(L x*u x*D x) := by
    funext x
    dsimp [D]
    ring
  rw [he]
  have hLa : Integrable (fun x => a^2*(L x*u x)^2) μ := hLu.const_mul (a^2)
  have hCa : Integrable (fun x => (2*a)*(L x*u x*D x)) μ := hC.const_mul (2*a)
  have hsum : Integrable (fun x => (D x)^2+a^2*(L x*u x)^2) μ := hDu.add hLa
  rw [integral_add hsum hCa,integral_add hDu hLa,integral_const_mul,integral_const_mul]
  change _=(∫ x,(D x)^2 ∂μ)+_ - _
  nlinarith [congrArg (fun t : ℝ => a*t) hz]

theorem compact_real_oscillator_directional_bound (L : E →L[ℝ] ℝ) (v : E) (hLv : L v=1)
    {u : E → ℝ} (hu : ContDiff ℝ 1 u) (hc : HasCompactSupport u) (a : ℝ) :
    a*(∫ x, (u x)^2 ∂μ) ≤
      (∫ x, (fderiv ℝ u x v)^2 ∂μ)+a^2*(∫ x, (L x*u x)^2 ∂μ) := by
  have h : (0:ℝ) ≤ ∫ x, (fderiv ℝ u x v+a*L x*u x)^2 ∂μ :=
    integral_nonneg (fun x => sq_nonneg _)
  rw [compact_real_oscillator_square L v hLv hu hc a] at h
  linarith

#print axioms compact_real_oscillator_square
#print axioms compact_real_oscillator_directional_bound
end TheoremT.Continuum
