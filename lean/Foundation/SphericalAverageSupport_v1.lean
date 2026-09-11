import SphericalAverage_v1
import PositiveHalfLineRestriction_v1

/-! Actual compact support and zero-boundary radial profiles for spherical
averages. Uniform support bounds are derived from the physical support of f,
not supplied as an extra property of its angular average. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem norm_radius_smul_sphere (r : ℝ) (w : Metric.sphere (0 : E) 1) :
    ‖r • w.val‖ = |r| := by
  have hw : ‖w.val‖ = 1 := by simpa only [Metric.mem_sphere, dist_zero_right] using w.property
  rw [norm_smul, Real.norm_eq_abs, hw, mul_one]

theorem sphereAverage_eq_zero_of_uniform (f : E → ℂ) (r : ℝ)
    (h : ∀ w : Metric.sphere (0 : E) 1, f (r • w.val) = 0) : sphereAverage f r = 0 := by
  apply integral_eq_zero_of_ae
  exact Filter.Eventually.of_forall h

theorem sphereAverage_compact {f : E → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (sphereAverage f) := by
  obtain ⟨R, hR⟩ := (show IsCompact (tsupport f) from hfc).isBounded.exists_norm_le
  have hs : Function.support (sphereAverage f) ⊆ Metric.closedBall (0 : ℝ) R := by
    intro r hr
    change dist r 0 ≤ R
    rw [dist_zero_right, Real.norm_eq_abs]
    by_contra hn
    have hzero : sphereAverage f r = 0 := by
      apply sphereAverage_eq_zero_of_uniform
      intro w
      apply image_eq_zero_of_notMem_tsupport
      intro hmem
      have hb := hR (r • w.val) hmem
      rw [norm_radius_smul_sphere] at hb
      exact hn hb
    exact hr hzero
  exact (isCompact_closedBall (0 : ℝ) R).of_isClosed_subset (isClosed_tsupport _)
    (closure_minimal hs Metric.isClosed_closedBall)

theorem sphereAverage_zero_not_tsupport {f : E → ℂ} (hf0 : (0 : E) ∉ tsupport f) :
    (0 : ℝ) ∉ tsupport (sphereAverage f) := by
  obtain ⟨ε,hε,hεball⟩ := Metric.mem_nhds_iff.mp
    ((isClosed_tsupport f).isOpen_compl.mem_nhds hf0)
  have hzero (r : ℝ) (hr : |r| < ε) : sphereAverage f r = 0 := by
    apply sphereAverage_eq_zero_of_uniform
    intro w
    apply image_eq_zero_of_notMem_tsupport
    apply hεball
    simpa only [Metric.mem_ball, dist_zero_right, norm_radius_smul_sphere] using hr
  have hs : Function.support (sphereAverage f) ⊆ {r : ℝ | ε ≤ |r|} := by
    intro r hr
    by_contra hn
    exact hr (hzero r (not_le.mp hn))
  have ht := closure_minimal hs (isClosed_le continuous_const continuous_abs)
  intro hmem
  have hh := ht hmem
  change ε ≤ |(0 : ℝ)| at hh
  rw [abs_zero] at hh
  exact (not_le.mpr hε) hh

def radialMeanProfile (f : E → ℂ) (r : ℝ) : ℂ := r • sphereAverage f r

theorem radialMeanProfile_contDiff {f : E → ℂ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (radialMeanProfile f) := contDiff_id.smul (sphereAverage_contDiff hf)

theorem radialMeanProfile_compact {f : E → ℂ} (hfc : HasCompactSupport f) :
    HasCompactSupport (radialMeanProfile f) := by
  change HasCompactSupport (fun r : ℝ => r • sphereAverage f r)
  exact HasCompactSupport.smul_left (f := fun r : ℝ => r) (sphereAverage_compact hfc)

theorem radialMeanProfile_zero_not_tsupport {f : E → ℂ} (hf0 : (0 : E) ∉ tsupport f) :
    (0 : ℝ) ∉ tsupport (radialMeanProfile f) :=
  fun h => sphereAverage_zero_not_tsupport hf0 (tsupport_smul_subset_right (fun r : ℝ => r)
    (sphereAverage f) h)

theorem radialMeanProfile_hasDerivAt {f : E → ℂ} (hf : ContDiff ℝ ∞ f) (r : ℝ) :
    HasDerivAt (radialMeanProfile f)
      (sphereAverage f r + r •
        (∫ w : Metric.sphere (0 : E) 1, fderiv ℝ f (r • w.val) w.val ∂sphereMeasure)) r := by
  have h := (hasDerivAt_id r).smul (sphereAverage_hasDerivAt hf r)
  have he : (id : ℝ → ℝ) • sphereAverage f = radialMeanProfile f := by
    funext s
    rfl
  rw [he] at h
  simpa only [id_eq, one_smul, add_comm] using h

def radialMeanTest (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hf0 : (0 : E) ∉ tsupport f) : TheoremT.HalfLine.Test :=
  TheoremT.OneDimensional.positiveRestrictionTest (radialMeanProfile f)
    (radialMeanProfile_contDiff hf) (radialMeanProfile_compact hfc)
    (radialMeanProfile_zero_not_tsupport hf0)

theorem radialMeanTest_value_of_pos (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hf0 : (0 : E) ∉ tsupport f) {r : ℝ} (hr : 0 < r) :
    (radialMeanTest f hf hfc hf0 : ℝ → ℂ) r = r • sphereAverage f r :=
  TheoremT.OneDimensional.positiveRestrictionTest_value_of_pos _ _ _ _ hr

theorem radialMeanTest_deriv_of_pos (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (hfc : HasCompactSupport f) (hf0 : (0 : E) ∉ tsupport f) {r : ℝ} (hr : 0 < r) :
    deriv (radialMeanTest f hf hfc hf0 : ℝ → ℂ) r =
      sphereAverage f r + r •
        (∫ w : Metric.sphere (0 : E) 1, fderiv ℝ f (r • w.val) w.val ∂sphereMeasure) := by
  rw [radialMeanTest, TheoremT.OneDimensional.positiveRestrictionTest_deriv_of_pos _ _ _ _ hr]
  exact (radialMeanProfile_hasDerivAt hf r).deriv

#print axioms sphereAverage_compact
#print axioms sphereAverage_zero_not_tsupport
#print axioms radialMeanProfile_hasDerivAt
#print axioms radialMeanTest
#print axioms radialMeanTest_deriv_of_pos
end TheoremT.Polar
