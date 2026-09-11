import CompactCutoffDirectionalEnergy_v1

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_weighted_cutoff_directional_energy {w η : E → ℝ} {u : E → F}
    (hw : ContDiff ℝ ∞ w) (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hu : ContDiff ℝ ∞ u) (v : E) (hw0 : ∀ x, fderiv ℝ w x v = 0) :
    (∫ x, (w x)^2*‖fderiv ℝ (fun y => η y • u y) x v‖^2 ∂μ) =
      -(∫ x, (w x)^2*inner ℝ ((η x)^2 • u x)
        (fderiv ℝ (fun y => fderiv ℝ u y v) x v) ∂μ) +
      (∫ x, (w x)^2*‖(fderiv ℝ η x v) • u x‖^2 ∂μ) := by
  have hcm : HasCompactSupport (fun x => w x*η x) := hc.mul_left
  have hηu : ContDiff ℝ ∞ (fun y => η y • u y) := hη.smul hu
  have h := compact_cutoff_directional_energy (μ := μ) (hw.mul hη) hcm hu v
  have he (x : E) : fderiv ℝ (fun y => (w y*η y) • u y) x v =
      w x • fderiv ℝ (fun y => η y • u y) x v := by
    have heq : (fun y => (w y*η y) • u y) = (fun y => w y • (η y • u y)) := by
      funext y
      exact mul_smul (w y) (η y) (u y)
    rw [heq,cutoff_directional_product hw hηu,hw0 x,zero_smul,zero_add]
  have hd (x : E) : fderiv ℝ (fun y => w y*η y) x v = w x*fderiv ℝ η x v := by
    simpa only [smul_eq_mul,hw0 x,zero_mul,zero_add] using cutoff_directional_product hw hη x v
  simp_rw [he,hd] at h
  simpa only [mul_pow,mul_smul,real_inner_smul_left,norm_smul,
    Real.norm_eq_abs,sq_abs,mul_assoc] using h

#print axioms compact_weighted_cutoff_directional_energy
end TheoremT.Continuum
