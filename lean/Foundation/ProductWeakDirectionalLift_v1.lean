import ProductWeakEllipticGain_v1

/-! The converse exact coordinate transport for genuine weak directional jets. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem productEuclideanLift_test
    (f : Lp ℂ 2 (volume : Measure (Y × T))) (φ : WithLp 2 (Y × T) → ℝ) :
    (∫ q, φ q • productEuclideanLift f q) = ∫ p, φ (WithLp.toLp 2 p) • f p := by
  calc
    _ = ∫ q, φ q • f q.ofLp := by
      apply integral_congr_ae
      filter_upwards [productEuclideanLift_ae f] with q hq
      rw [hq]
      rfl
    _ = _ := by
      have hh := (WithLp.volume_preserving_ofLp Y T).integral_comp
        (WithLp.prodContinuousLinearEquiv 2 ℝ Y T).toHomeomorph.measurableEmbedding
        (fun p : Y × T => φ (WithLp.toLp 2 p) • f p)
      simpa only [WithLp.toLp_ofLp] using hh

theorem weakL2Directional_productEuclideanLift
    {f g : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (h : WeakProductL2Directional f g v) :
    WeakL2Directional (productEuclideanLift f) (productEuclideanLift g)
      (WithLp.toLp 2 v) := by
  intro φ hφ hc
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ Y T).symm
  have htest : ContDiff ℝ ∞ (φ ∘ e) := hφ.comp e.contDiff
  have hsupport : HasCompactSupport (φ ∘ e) := hc.comp_homeomorph e.toHomeomorph
  have hchain (p : Y × T) :
      fderiv ℝ (φ ∘ e) p v = fderiv ℝ φ (WithLp.toLp 2 p) (WithLp.toLp 2 v) := by
    have hh := ((hφ.differentiable (by simp)).differentiableAt.hasFDerivAt).comp p e.hasFDerivAt
    rw [hh.fderiv]
    rfl
  rw [productEuclideanLift_test, productEuclideanLift_test]
  have hh := h (φ ∘ e) htest hsupport
  have heq (p : Y × T) : e p = WithLp.toLp 2 p := rfl
  simpa only [Function.comp_apply, hchain, heq] using hh

theorem productEuclideanUnlift_directional_chain
    {u : WithLp 2 (Y × T) → ℂ} (hu : ContDiff ℝ ∞ u) (p v : Y × T) :
    fderiv ℝ (u ∘ WithLp.toLp 2) p v =
      fderiv ℝ u (WithLp.toLp 2 p) (WithLp.toLp 2 v) := by
  let e := (WithLp.prodContinuousLinearEquiv 2 ℝ Y T).symm
  have hh := ((hu.differentiable (by simp)).differentiableAt.hasFDerivAt).comp p e.hasFDerivAt
  change HasFDerivAt (𝕜 := ℝ) (u ∘ WithLp.toLp 2) _ p at hh
  rw [hh.fderiv]
  rfl

theorem productEuclideanUnlift_second_directional_chain
    {u : WithLp 2 (Y × T) → ℂ} (hu : ContDiff ℝ ∞ u) (p v w : Y × T) :
    fderiv ℝ (fun z => fderiv ℝ (u ∘ WithLp.toLp 2) z v) p w =
      fderiv ℝ (fun q => fderiv ℝ u q (WithLp.toLp 2 v))
        (WithLp.toLp 2 p) (WithLp.toLp 2 w) := by
  have he : (fun z => fderiv ℝ (u ∘ WithLp.toLp 2) z v) =
      (fun q => fderiv ℝ u q (WithLp.toLp 2 v)) ∘ WithLp.toLp 2 := by
    funext z
    exact productEuclideanUnlift_directional_chain hu z v
  rw [he]
  apply productEuclideanUnlift_directional_chain
  exact (hu.fderiv_right (by simp)).clm_apply contDiff_const

end TheoremT.Continuum
