import HydrogenRegularizedSquare_v1
import HardyLimitCompact_v1

noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Filter
open scoped BigOperators Topology
namespace TheoremT.Hydrogen
open TheoremT.Hardy

theorem compact_real_square_integrable {u : R3 → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    Integrable (fun x => (u x)^2) := by
  apply (hu.pow 2).integrable_of_hasCompactSupport
  simpa only [sq] using huc.mul_right (f' := u)

theorem compact_real_gradient_integrable {u : R3 → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x => ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) := by
  apply integrable_finsetSum
  intro i _
  exact compact_real_square_integrable
    ((hu.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)) (huc.fderiv_apply ℝ (basisVector i))

theorem regularized_coulomb_integrable {u : R3 → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) {δ : ℝ} (hδ : 0 < δ) :
    Integrable (fun x => (u x)^2 / Real.sqrt (‖x‖^2 + δ)) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (hu.pow 2).div (((continuous_norm.pow 2).add continuous_const).sqrt)
      (fun x => (Real.sqrt_pos.2 (regularizedDenominator_pos hδ x)).ne')
  · apply huc.mono
    intro x hx
    simp only [Function.mem_support] at hx ⊢
    intro hz
    apply hx
    rw [hz]
    norm_num

theorem regularized_coulomb_integral {δ t : ℝ} (hδ : 0 < δ) (ht : 0 ≤ t)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    2 * t * (∫ x, (u x)^2 / Real.sqrt (‖x‖^2 + δ)) ≤
      (∫ x, ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) +
        t^2 * (∫ x, (u x)^2) := by
  have hg := compact_real_gradient_integrable hu huc
  have hu2 := compact_real_square_integrable hu.continuous huc
  have hw : Integrable (fun x => ∑ i : Fin 3,
      fderiv ℝ (radialWeightedField δ u i) x (basisVector i)) := by
    apply integrable_finsetSum
    intro i _
    exact (((radialWeightedField_contDiff hδ hu i).continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
        ((radialWeightedField_compact huc i).fderiv_apply ℝ (basisVector i))
  have hf := regularized_coulomb_integrable hu.continuous huc hδ
  have h := integral_mono (hf.const_mul (2*t))
    ((hg.add (hu2.const_mul (t^2))).add (hw.const_mul t))
    (fun x => by simpa only [Pi.add_apply, mul_div_assoc] using
      regularized_coulomb_pointwise hδ ht hu x)
  simp only [Pi.add_apply] at h
  have hsum := integral_add (hg.add (hu2.const_mul (t^2))) (hw.const_mul t)
  have hsum2 := integral_add hg (hu2.const_mul (t^2))
  simp only [Pi.add_apply] at hsum hsum2
  rw [hsum, hsum2, integral_const_mul, integral_const_mul, integral_const_mul,
    radialWeightedField_divergence_integral hδ hu huc] at h
  simpa using h

/-- The exact constant-one Coulomb uncertainty family for real compact C¹ functions.
For every t>0, 2t times the Coulomb expectation is bounded by kinetic energy+t² mass. -/
theorem compact_real_coulomb_bound {t : ℝ} (ht : 0 < t)
    {u : R3 → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x => (u x)^2 / ‖x‖) ∧
      2 * t * (∫ x, (u x)^2 / ‖x‖) ≤
        (∫ x, ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) +
          t^2 * (∫ x, (u x)^2) := by
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hδ : ∀ n, 0 < δ n := by intro n; dsimp [δ]; positivity
  let B := ((∫ x, ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) +
    t^2 * (∫ x, (u x)^2)) / (2*t)
  have hb : ∀ n, (∫ x, (u x)^2 / Real.sqrt (‖x‖^2 + δ n)) ≤ B := by
    intro n
    apply (le_div_iff₀ (by positivity : 0 < 2*t)).2
    simpa only [mul_comm] using regularized_coulomb_integral (hδ n) ht.le hu huc
  have hf := TheoremT.HardyLimit.integrable_and_integral_le_of_nonneg_limit
    (fun n => regularized_coulomb_integrable hu.continuous huc (hδ n))
    (fun n => Filter.Eventually.of_forall (fun x => by positivity))
    (Filter.Eventually.of_forall (fun x => div_nonneg (sq_nonneg (u x)) (norm_nonneg x)))
    (B := B) ?_ hb ?_
  · refine ⟨hf.1, ?_⟩
    have h := (le_div_iff₀ (by positivity : 0 < 2*t)).1 hf.2
    simpa only [mul_comm] using h
  · filter_upwards [volume.ae_ne (0 : R3)] with x hx
    have hdlim : Tendsto δ atTop (𝓝 (0 : ℝ)) := tendsto_one_div_add_atTop_nhds_zero_nat
    have hden : Tendsto (fun n => Real.sqrt (‖x‖^2 + δ n)) atTop (𝓝 ‖x‖) := by
      have hden0 : Tendsto (fun n => ‖x‖^2 + δ n) atTop (𝓝 (‖x‖^2)) := by
        simpa only [add_zero] using (tendsto_const_nhds (x := ‖x‖^2)).add hdlim
      simpa only [Function.comp_def, Real.sqrt_sq (norm_nonneg x)] using
        (Real.continuous_sqrt.tendsto (‖x‖^2)).comp hden0
    exact tendsto_const_nhds.div hden (norm_ne_zero_iff.mpr hx)
  · exact (integral_nonneg (fun x => by positivity)).trans (hb 0)

#print axioms regularized_coulomb_integral
#print axioms compact_real_coulomb_bound
end TheoremT.Hydrogen
