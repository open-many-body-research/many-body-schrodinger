import ProductWeakDirectionalLift_v1

/-! Derivative and representative transport used by the genuine product cutoff
jet theorem. The coordinate map preserves actual product Lebesgue measure. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem productEuclideanLift_toLp_ae
    (f : Lp ℂ 2 (volume : Measure (Y × T))) :
    (fun p => productEuclideanLift f (WithLp.toLp 2 p)) =ᵐ[volume] f := by
  change ∀ᵐ p : Y × T ∂(volume : Measure (Y × T)),
    productEuclideanLift f (WithLp.toLp 2 p) = f p
  simpa only [Function.comp_apply,WithLp.ofLp_toLp] using
    (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae (productEuclideanLift_ae f)

theorem product_cutoff_lift_directional
    {χ : Y × T → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (q : WithLp 2 (Y × T)) (v : Y × T) :
    fderiv ℝ (χ ∘ WithLp.ofLp) q (WithLp.toLp 2 v) = fderiv ℝ χ q.ofLp v := by
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ Y T
  have hh := ((hχ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp q c.hasFDerivAt
  change HasFDerivAt (𝕜 := ℝ) (χ ∘ WithLp.ofLp) _ q at hh
  rw [hh.fderiv]
  rfl

theorem product_cutoff_lift_second_directional
    {χ : Y × T → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (q : WithLp 2 (Y × T)) (v w : Y × T) :
    fderiv ℝ (fun r => fderiv ℝ (χ ∘ WithLp.ofLp) r (WithLp.toLp 2 v)) q
      (WithLp.toLp 2 w) = fderiv ℝ (fun p => fderiv ℝ χ p v) q.ofLp w := by
  have he : (fun r => fderiv ℝ (χ ∘ WithLp.ofLp) r (WithLp.toLp 2 v)) =
      (fun p => fderiv ℝ χ p v) ∘ WithLp.ofLp :=
    funext (fun r => product_cutoff_lift_directional hχ r v)
  rw [he]
  apply product_cutoff_lift_directional
  exact (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const

#print axioms productEuclideanLift_toLp_ae
#print axioms product_cutoff_lift_directional
#print axioms product_cutoff_lift_second_directional
end TheoremT.Continuum
