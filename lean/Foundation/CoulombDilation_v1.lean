import ContinuumFoundation_v1
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! Exact positive-dilation homogeneity and potential-energy scaling for the
original continuum Coulomb potential. The integrability theorem is separate
from the Bochner integral identity, so the latter's zero convention for
nonintegrable functions cannot silently certify an energy expectation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem position_real_smul {N : ℕ} (R : ℝ) (x : Configuration N) (i : Fin N) :
    position (R • x) i = R • position x i := by
  apply (WithLp.ext_iff 2).mpr
  funext k
  rfl

theorem coulombPotential_smul (N : ℕ) (Z : ℝ) {R : ℝ} (hR : 0 < R)
    (x : Configuration N) :
    coulombPotential N Z (R • x) = R⁻¹ * coulombPotential N Z x := by
  have hn (i : Fin N) :
      ‖position (R • x) i‖⁻¹ = R⁻¹ * ‖position x i‖⁻¹ := by
    rw [position_real_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hR, mul_inv_rev]
    ring
  have hp (i j : Fin N) :
      ‖position (R • x) i - position (R • x) j‖⁻¹ =
        R⁻¹ * ‖position x i - position x j‖⁻¹ := by
    rw [position_real_smul, position_real_smul, ← smul_sub, norm_smul,
      Real.norm_eq_abs, abs_of_pos hR, mul_inv_rev]
    ring
  simp only [coulombPotential, hn, hp]
  simp_rw [← Finset.mul_sum]
  ring

theorem coulombPotential_eq_inv_dilated (N : ℕ) (Z : ℝ) {R : ℝ}
    (hR : 0 < R) (x : Configuration N) :
    coulombPotential N Z x = R⁻¹ * coulombPotential N Z (R⁻¹ • x) := by
  rw [coulombPotential_smul N Z (inv_pos.mpr hR), inv_inv,
    ← mul_assoc, inv_mul_cancel₀ hR.ne', one_mul]

theorem coulomb_dilation_energy_integrable {N : ℕ} (Z : ℝ)
    (u : Configuration N → ℂ) {R : ℝ} (hR : 0 < R)
    (hu : Integrable (fun x => coulombPotential N Z x * ‖u x‖^2) volume) :
    Integrable (fun x => coulombPotential N Z x * ‖u (R⁻¹ • x)‖^2) volume := by
  have h := (hu.comp_smul (inv_ne_zero hR.ne')).const_mul R⁻¹
  convert h using 1
  funext x
  rw [coulombPotential_eq_inv_dilated N Z hR x]
  ring

theorem coulomb_dilation_energy_integral (N : ℕ) (Z : ℝ)
    (u : Configuration N → ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ x, coulombPotential N Z x * ‖u (R⁻¹ • x)‖^2) =
      R ^ Module.finrank ℝ (Configuration N) * R⁻¹ *
        (∫ x, coulombPotential N Z x * ‖u x‖^2) := by
  have hfun : (fun x => coulombPotential N Z x * ‖u (R⁻¹ • x)‖^2) =
      (fun x => R⁻¹ * (coulombPotential N Z (R⁻¹ • x) * ‖u (R⁻¹ • x)‖^2)) := by
    funext x
    rw [coulombPotential_eq_inv_dilated N Z hR x]
    ring
  rw [hfun, integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg volume
      (fun x => coulombPotential N Z x * ‖u x‖^2) hR.le]
  simp only [smul_eq_mul]
  ring

theorem coulomb_dilation_energy_integral_dimension (N : ℕ) (Z : ℝ)
    (u : Configuration N → ℂ) {R : ℝ} (hR : 0 < R) :
    (∫ x, coulombPotential N Z x * ‖u (R⁻¹ • x)‖^2) =
      R ^ (N * 3) * R⁻¹ * (∫ x, coulombPotential N Z x * ‖u x‖^2) := by
  simpa only [Configuration, Coordinate, finrank_euclideanSpace, Fintype.card_prod,
    Fintype.card_fin] using coulomb_dilation_energy_integral N Z u hR

#print axioms coulombPotential_smul
#print axioms coulomb_dilation_energy_integrable
#print axioms coulomb_dilation_energy_integral
#print axioms coulomb_dilation_energy_integral_dimension

end TheoremT.Continuum
