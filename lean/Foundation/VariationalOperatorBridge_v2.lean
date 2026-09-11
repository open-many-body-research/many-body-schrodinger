import FermionicTrialL2_v2
import HardyCoulombSymmetry_v2
import SpectralBottom_v2

/-! The original normalized continuum variational infimum is the greatest form
lower bound of the actual Coulomb partial operator. No self-adjointness or
spectral identification is assumed or concluded by this bridge. -/

noncomputable section
open MeasureTheory
open scoped BigOperators LinearPMap

namespace TheoremT.Continuum

theorem rayleighNumerator_eq_re_complex_inner {N : ℕ} (ψ h : SpinSpace N) :
    rayleighNumerator ψ h = (inner ℂ ψ h).re := by
  simp only [rayleighNumerator, PiLp.inner_apply, Complex.re_sum]

theorem rayleighNumerator_real_smul {N : ℕ} (r : ℝ) (ψ h : SpinSpace N) :
    rayleighNumerator ((r : ℂ) • ψ) ((r : ℂ) • h) = r^2 * rayleighNumerator ψ h := by
  rw [rayleighNumerator_eq_re_complex_inner, rayleighNumerator_eq_re_complex_inner,
    inner_smul_left, inner_smul_right]
  simp [Complex.mul_re, pow_two, mul_assoc]

theorem operatorLowerBounds_coulomb_iff (N : ℕ) (Z a : ℝ) :
    a ∈ TheoremT.OperatorTheory.operatorLowerBounds (coulombPartialOperator N Z) ↔
      (a : EReal) ≤ variationalGroundEnergy N Z := by
  constructor
  · intro ha
    apply le_sInf
    rintro E ⟨ψ, h, hn, hg, rfl⟩
    let ψF : FermionicSpace N := ⟨ψ, hg.1⟩
    let hF : FermionicSpace N := ⟨h, hg.2.1⟩
    have hdom : ψF ∈ (coulombPartialOperator N Z).domain :=
      (coulombPartialOperator_domain_iff N Z ψF).mpr ⟨hF, hg⟩
    let x : (coulombPartialOperator N Z).domain := ⟨ψF, hdom⟩
    have heq : (coulombPartialOperator N Z x).val = h :=
      hamiltonian_graph_unique (coulombPartialOperator_apply_graph N Z x) hg
    have hb := ha x
    change a * ‖ψ‖^2 ≤ (inner ℂ ψ (coulombPartialOperator N Z x).val).re at hb
    rw [heq, hn, one_pow, mul_one, ← rayleighNumerator_eq_re_complex_inner] at hb
    exact_mod_cast hb
  · intro ha
    intro x
    let ψ : SpinSpace N := x.val.val
    let h : SpinSpace N := (coulombPartialOperator N Z x).val
    have hg : hamiltonianGraph N Z ψ h := coulombPartialOperator_apply_graph N Z x
    change a * ‖ψ‖^2 ≤ (inner ℂ ψ h).re
    rw [← rayleighNumerator_eq_re_complex_inner]
    by_cases hz : ψ = 0
    · rw [hz, rayleighNumerator_eq_re_complex_inner]
      simp
    · have hn0 : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hz
      let r : ℝ := ‖ψ‖⁻¹
      have hn : ‖(r : ℂ) • ψ‖ = 1 := by
        rw [_root_.norm_smul, Complex.norm_real]
        dsimp [r]
        rw [abs_inv, abs_of_nonneg (norm_nonneg ψ), inv_mul_cancel₀ hn0]
      have hgn := hamiltonian_graph_smul (r : ℂ) hg
      have hle := ha.trans (variational_ground_le_trial hn hgn)
      have hreal : a ≤ rayleighNumerator ((r : ℂ) • ψ) ((r : ℂ) • h) := by exact_mod_cast hle
      rw [rayleighNumerator_real_smul] at hreal
      have hdiv : a ≤ rayleighNumerator ψ h / ‖ψ‖^2 := by
        simpa only [r, inv_pow, div_eq_mul_inv, mul_comm] using hreal
      exact (le_div_iff₀ (sq_pos_of_ne_zero hn0)).mp hdiv

/-- Exact normalized variational/form lower-bound identification for the actual
continuum Coulomb operator. Its hypotheses do not assume a spectral assertion. -/
theorem variational_energy_isGreatest_operatorLowerBounds (N : ℕ) (Z : ℝ) :
    IsGreatest (TheoremT.OperatorTheory.operatorLowerBounds (coulombPartialOperator N Z))
      (variationalGroundEnergy N Z).toReal := by
  have hfinite := variational_ground_energy_finite N Z
  have hcoe := EReal.coe_toReal hfinite.1 hfinite.2
  constructor
  · apply (operatorLowerBounds_coulomb_iff N Z _).mpr
    exact hcoe.le
  · intro a ha
    have hle := (operatorLowerBounds_coulomb_iff N Z a).mp ha
    rw [← hcoe] at hle
    exact_mod_cast hle

#print axioms rayleighNumerator_eq_re_complex_inner
#print axioms rayleighNumerator_real_smul
#print axioms operatorLowerBounds_coulomb_iff
#print axioms variational_energy_isGreatest_operatorLowerBounds

end TheoremT.Continuum
