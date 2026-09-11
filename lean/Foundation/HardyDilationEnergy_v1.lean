import HardyDilationSpin_v1
import CoulombDilation_v1
import CoulombH1IntegralForm_v1

/-! Exact physical form energy of dilated compact fermionic trials. All L²
representatives are connected by almost-everywhere equality to the raw trial,
and potential energy is proved integrable independently of the Bochner convention. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

def smoothCoreKinetic {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : ℝ :=
  (1 / 2 : ℝ) * ∑ k, ‖smoothCoreSpinDerivative hu hc k‖^2

def smoothCorePotential {N : ℕ} (Z : ℝ) (u : Configuration N → ℂ) : ℝ :=
  (Fintype.card (SpinConfiguration N) : ℝ) *
    ∫ x, coulombPotential N Z x * ‖u x‖^2

def smoothCoreEnergy {N : ℕ} (Z : ℝ) {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) : ℝ :=
  smoothCoreKinetic hu hc + smoothCorePotential Z u

theorem smoothCore_potential_integrable {N : ℕ} (Z : ℝ) {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    Integrable (fun x => coulombPotential N Z x * ‖u x‖^2) volume := by
  let f := smoothCoreL2 hu hc
  have hf : HasH1 f := h2_implies_h1 (smoothCoreL2_hasH2 hu hc)
  have hV := coulombProductL2_of_hasH1 Z hf
  let v : SpatialL2 N := hV.toLp _
  have hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x := hV.coeFn_toLp
  apply (coulomb_potential_energy_integrable hv).congr
  filter_upwards [smoothCoreL2_ae hu hc] with x hx
  change coulombPotential N Z x * ‖smoothCoreL2 hu hc x‖^2 = _
  rw [hx]

theorem smoothCoreSpin_formValue {N : ℕ} (Z : ℝ) {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u)
    (halt : ∀ (π : Equiv.Perm (Fin N)) x,
      u (permuteSpace π x) = permutationSign π * u x) :
    coulombH1FormValue N Z (smoothCoreSpin hu hc) (smoothCoreEnergy Z hu hc) := by
  apply coulombH1FormValue_iff_integral.mpr
  refine ⟨(smoothCoreSpin_mem_target hu hc halt).1, smoothCoreSpinDerivative hu hc,
    smoothCoreSpin_weakPartial hu hc, ?_⟩
  unfold smoothCoreEnergy smoothCoreKinetic smoothCorePotential
  congr 1
  have he (σ : SpinConfiguration N) :
      (∫ x, coulombPotential N Z x * ‖smoothCoreSpin hu hc σ x‖^2) =
        ∫ x, coulombPotential N Z x * ‖u x‖^2 := by
    apply integral_congr_ae
    filter_upwards [smoothCoreL2_ae hu hc] with x hx
    change coulombPotential N Z x * ‖smoothCoreL2 hu hc x‖^2 = _
    rw [hx]
  simp only [he, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

theorem spatialDilation_coreEnergy {N : ℕ} (Z : ℝ) {u : Configuration N → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) {R : ℝ} (hR : 0 < R) :
    smoothCoreEnergy Z (spatialDilation_contDiff hu R) (spatialDilation_compact hc hR) =
      R ^ Module.finrank ℝ (Configuration N) *
        ((R⁻¹)^2 * smoothCoreKinetic hu hc + R⁻¹ * smoothCorePotential Z u) := by
  unfold smoothCoreEnergy smoothCoreKinetic smoothCorePotential
  rw [spatialDilation_spin_gradient_sq hu hc hR]
  change (1 / 2 : ℝ) * ((R⁻¹)^2 * R ^ Module.finrank ℝ (Configuration N) * _) +
    (Fintype.card (SpinConfiguration N) : ℝ) *
      (∫ x, coulombPotential N Z x * ‖u (R⁻¹ • x)‖^2) = _
  rw [coulomb_dilation_energy_integral N Z u hR]
  ring

#print axioms smoothCore_potential_integrable
#print axioms smoothCoreSpin_formValue
#print axioms spatialDilation_coreEnergy
end TheoremT.Continuum
