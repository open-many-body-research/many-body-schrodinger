import HardyDilationEnergy_v1
import CoulombH1Infimum_v1

/-! Every finite-electron one-nucleus continuum system has spectral/variational
infimum at most zero. This is a spreading-trial theorem: it makes no binding,
attainment, nondegeneracy, or spectral-gap assumption. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem operatorLowerBound_le_dilated_trial {N : ℕ} {Z a : ℝ}
    (ha : a ∈ TheoremT.OperatorTheory.operatorLowerBounds (coulombPartialOperator N Z))
    {u : Configuration N → ℂ} (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (halt : ∀ (π : Equiv.Perm (Fin N)) x,
      u (permuteSpace π x) = permutationSign π * u x)
    {R : ℝ} (hR : 0 < R) :
    a * ‖smoothCoreSpin hu hc‖^2 ≤
      (R⁻¹)^2 * smoothCoreKinetic hu hc + R⁻¹ * smoothCorePotential Z u := by
  have hform := smoothCoreSpin_formValue Z (spatialDilation_contDiff hu R)
    (spatialDilation_compact hc hR) (spatialDilation_alternating halt R)
  have hb := operatorLowerBound_on_h1Form ha _ _ hform
  rw [spatialDilation_spin_norm_sq hu hc hR, spatialDilation_coreEnergy Z hu hc hR] at hb
  have hM : 0 < R ^ Module.finrank ℝ (Configuration N) := pow_pos hR _
  apply (mul_le_mul_iff_left₀ hM).mp
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hb

theorem coulomb_operator_lowerBound_nonpositive {N : ℕ} {Z a : ℝ}
    (ha : a ∈ TheoremT.OperatorTheory.operatorLowerBounds (coulombPartialOperator N Z)) :
    a ≤ 0 := by
  let hu := fermionicTrialAmplitude_smooth N
  let hc := fermionicTrialAmplitude_compact N
  let T : ℝ := smoothCoreKinetic hu hc
  let P : ℝ := smoothCorePotential Z (fermionicTrialAmplitude N)
  have hi : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (nhds 0) := by
    simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hl : Tendsto (fun n : ℕ => (((n : ℝ) + 1)⁻¹)^2 * T +
      ((n : ℝ) + 1)⁻¹ * P) atTop (nhds 0) := by
    simpa using ((hi.pow 2).mul_const T).add (hi.mul_const P)
  have hb : a * ‖smoothCoreSpin hu hc‖^2 ≤ 0 := by
    apply le_of_tendsto_of_tendsto' tendsto_const_nhds hl
    intro n
    exact operatorLowerBound_le_dilated_trial ha hu hc
      (fermionicTrialAmplitude_alternating N) (by positivity : 0 < (n : ℝ) + 1)
  have hs : 0 < ‖smoothCoreSpin hu hc‖^2 := by
    change 0 < ‖fermionicTrialSpin N‖^2
    exact sq_pos_of_pos (norm_pos_iff.mpr (fermionicTrialSpin_ne_zero N))
  nlinarith

/-- Universal upper enclosure endpoint for the original continuum variational
energy, proved with actual compact fermionic H² trial dilations. -/
theorem variational_ground_energy_nonpositive (N : ℕ) (Z : ℝ) :
    variationalGroundEnergy N Z ≤ (0 : EReal) := by
  have h := coulomb_operator_lowerBound_nonpositive
    (variational_energy_isGreatest_operatorLowerBounds N Z).1
  have hf := variational_ground_energy_finite N Z
  rw [← EReal.coe_toReal hf.1 hf.2]
  exact_mod_cast h

#print axioms operatorLowerBound_le_dilated_trial
#print axioms coulomb_operator_lowerBound_nonpositive
#print axioms variational_ground_energy_nonpositive
end TheoremT.Continuum
