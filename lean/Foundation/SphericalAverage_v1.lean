import SphereParameterDerivative_v1

/-! Actual spherical averaging preserves global smoothness. Its radial
derivative is the sphere integral of the actual directional Fréchet derivative. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

def sphereAverage (f : E → ℂ) (r : ℝ) : ℂ :=
  ∫ w : Metric.sphere (0 : E) 1, f (r • w.val) ∂sphereMeasure

theorem sphereAverage_contDiff {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (sphereAverage f) :=
  jointSphereAverage_contDiff (hf.comp (contDiff_fst.smul contDiff_snd))

theorem radialJoint_radiusDerivative {f : E → ℂ} (hf : ContDiff ℝ ∞ f)
    (r : ℝ) (x : E) :
    jointRadiusDerivative (fun p : ℝ × E => f (p.1 • p.2)) (r,x) =
      fderiv ℝ f (r • x) x := by
  have hG : ContDiff ℝ ∞ (fun p : ℝ × E => f (p.1 • p.2)) :=
    hf.comp (contDiff_fst.smul contDiff_snd)
  have h₁ : HasDerivAt (fun s : ℝ => f (s • x))
      (jointRadiusDerivative (fun p : ℝ × E => f (p.1 • p.2)) (r,x)) r :=
    by
      simpa only [Function.comp_def, id_eq, jointRadiusDerivative] using
        (hG.differentiable (by simp) (r,x)).hasFDerivAt.comp_hasDerivAt r
          ((hasDerivAt_id r).prodMk (hasDerivAt_const r x))
  have h₂ : HasDerivAt (fun s : ℝ => f (s • x)) (fderiv ℝ f (r • x) x) r := by
    simpa only [Function.comp_def, id_eq, one_smul] using (hf.differentiable (by simp) (r • x)).hasFDerivAt.comp_hasDerivAt r
      ((hasDerivAt_id r).smul_const x)
  exact h₁.unique h₂

theorem sphereAverage_hasDerivAt {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    HasDerivAt (sphereAverage f)
      (∫ w : Metric.sphere (0 : E) 1, fderiv ℝ f (r • w.val) w.val ∂sphereMeasure) r := by
  have hG : ContDiff ℝ ∞ (fun p : ℝ × E => f (p.1 • p.2)) :=
    hf.comp (contDiff_fst.smul contDiff_snd)
  have h := jointSphereAverage_hasDerivAt hG r
  have he : jointSphereAverage (jointRadiusDerivative (fun p : ℝ × E => f (p.1 • p.2))) r =
      ∫ w : Metric.sphere (0 : E) 1, fderiv ℝ f (r • w.val) w.val ∂sphereMeasure := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun w => radialJoint_radiusDerivative hf r w.val)
  rw [he] at h
  exact h

theorem sphereAverage_deriv {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    deriv (sphereAverage f) r =
      ∫ w : Metric.sphere (0 : E) 1, fderiv ℝ f (r • w.val) w.val ∂sphereMeasure :=
  (sphereAverage_hasDerivAt hf r).deriv

#print axioms sphereAverage_contDiff
#print axioms radialJoint_radiusDerivative
#print axioms sphereAverage_hasDerivAt
#print axioms sphereAverage_deriv
end TheoremT.Polar
