import HardyConvolutionAverage_v1
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! Genuine normalized nonnegative convolution L² contraction, with density and
integral identities proved explicitly. -/
noncomputable section
set_option maxHeartbeats 500000
open MeasureTheory
namespace TheoremT.HardyConvolution

/-- Convolution with an integrable nonnegative kernel of integral one is an L²
contraction. The reference measure is right translation invariant and sigma finite;
the vector-valued input uses a strongly measurable representative. -/
theorem normalized_convolution_memLp_two_and_bound
    {G E : Type*} [AddCommGroup G] [MeasurableSpace G]
    [MeasurableAdd₂ G] [MeasurableNeg G]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {μ : Measure G} [SFinite μ] [μ.IsAddRightInvariant]
    {ρ : G → ℝ} (hρm : Measurable ρ) (hρn : ∀ x, 0 ≤ ρ x)
    (hρi : Integrable ρ μ) (hρone : (∫ x, ρ x ∂μ) = 1)
    {f : G → E} (hfM : StronglyMeasurable f) (hf : MemLp f 2 μ) :
    MemLp (fun x => ∫ t, ρ t • f (x - t) ∂μ) 2 μ ∧
      (∫ x, ‖∫ t, ρ t • f (x - t) ∂μ‖^2 ∂μ) ≤ (∫ x, ‖f x‖^2 ∂μ) := by
  let η : Measure G := μ.withDensity (fun x => ENNReal.ofReal (ρ x))
  have hmass : η Set.univ = 1 := by
    dsimp [η]
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
      ← ofReal_integral_eq_lintegral_ofReal hρi (Filter.Eventually.of_forall hρn),
      hρone, ENNReal.ofReal_one]
  let : IsProbabilityMeasure η := ⟨hmass⟩
  have hEq (x : G) : (∫ t, f (x - t) ∂η) = ∫ t, ρ t • f (x - t) ∂μ := by
    dsimp [η]
    rw [integral_withDensity_eq_integral_toReal_smul hρm.ennreal_ofReal
      (Filter.Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
    apply integral_congr_ae
    filter_upwards with t
    change (ENNReal.ofReal (ρ t)).toReal • f (x - t) = ρ t • f (x - t)
    rw [ENNReal.toReal_ofReal (hρn t)]
  simpa only [hEq] using probability_average_memLp_two_and_bound (η := η) hfM hf

set_option pp.proofs false in
#print normalized_convolution_memLp_two_and_bound
#print axioms normalized_convolution_memLp_two_and_bound
end TheoremT.HardyConvolution
