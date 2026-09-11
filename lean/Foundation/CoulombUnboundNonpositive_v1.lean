import CoulombNonattainment_v1
import HardyGroundNonpositive_v1
import CoulombSpectralBottom_v2
import NonrealResolvent_v2

/-! A fully identified parameter class with spectral infimum zero and no
normalized minimizing vector. The exclusion N=0 in nonattainment is essential. -/
noncomputable section
open scoped LinearPMap

namespace TheoremT.Continuum

theorem variational_ground_energy_eq_zero_of_charge_nonpos (N : ℕ)
    {Z : ℝ} (hZ : Z ≤ 0) : variationalGroundEnergy N Z = 0 := by
  apply le_antisymm (variational_ground_energy_nonpositive N Z)
  simpa only [max_eq_right hZ, zero_pow (by norm_num : 2 ≠ 0),
    mul_zero, zero_div, EReal.coe_zero] using variational_ground_energy_sharp_lower_bound N Z

theorem form_ground_energy_eq_zero_of_charge_nonpos (N : ℕ)
    {Z : ℝ} (hZ : Z ≤ 0) : formGroundEnergy N Z = 0 := by
  rw [formGroundEnergy_eq_variationalGroundEnergy,
    variational_ground_energy_eq_zero_of_charge_nonpos N hZ]

theorem zero_mem_coulomb_spectrum_of_charge_nonpos (N : ℕ) {Z : ℝ} (hZ : Z ≤ 0) :
    (0 : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z) := by
  have hm := coulomb_variational_energy_mem_spectrum N Z
  simpa only [variational_ground_energy_eq_zero_of_charge_nonpos N hZ,
    EReal.toReal_zero, Complex.ofReal_zero] using hm

theorem zero_isLeast_real_coulomb_spectrum_of_charge_nonpos (N : ℕ)
    {Z : ℝ} (hZ : Z ≤ 0) :
    IsLeast {t : ℝ | (t : ℂ) ∈
      TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z)} 0 := by
  have hm := coulomb_variational_energy_least_real_spectrum N Z
  simpa only [variational_ground_energy_eq_zero_of_charge_nonpos N hZ,
    EReal.toReal_zero] using hm

theorem nonpositive_charge_spectrum_real_nonnegative (N : ℕ) {Z : ℝ} (hZ : Z ≤ 0)
    {z : ℂ}
    (hz : z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z)) :
    z.im = 0 ∧ 0 ≤ z.re := by
  have hi := TheoremT.OperatorTheory.unboundedSpectrum_im_eq_zero _
    (coulombPartialOperator_selfAdjoint N Z) hz
  refine ⟨hi, ?_⟩
  apply (zero_isLeast_real_coulomb_spectrum_of_charge_nonpos N hZ).2
  change (z.re : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z)
  have heq : (z.re : ℂ) = z := by
    apply Complex.ext <;> simp [hi]
  rwa [heq]

theorem no_normalized_h1_minimizer_of_charge_nonpos {N : ℕ} (hN : 0 < N)
    {Z : ℝ} (hZ : Z ≤ 0) :
    ¬ ∃ ψ : SpinSpace N, ∃ q : ℝ, ‖ψ‖ = 1 ∧ coulombH1FormValue N Z ψ q ∧
      (q : EReal) = formGroundEnergy N Z := by
  rintro ⟨ψ, q, hn, hq, he⟩
  have hψ : ψ ≠ 0 := by intro hz; simpa [hz] using hn
  have hp := coulombH1FormValue_pos_of_charge_nonpos hN hZ hq hψ
  rw [form_ground_energy_eq_zero_of_charge_nonpos N hZ] at he
  have hz : q = 0 := by exact_mod_cast he
  linarith

theorem no_normalized_h2_minimizer_of_charge_nonpos {N : ℕ} (hN : 0 < N)
    {Z : ℝ} (hZ : Z ≤ 0) :
    ¬ ∃ ψ h : SpinSpace N, ‖ψ‖ = 1 ∧ hamiltonianGraph N Z ψ h ∧
      (rayleighNumerator ψ h : EReal) = variationalGroundEnergy N Z := by
  rintro ⟨ψ, h, hn, hg, he⟩
  apply no_normalized_h1_minimizer_of_charge_nonpos hN hZ
  refine ⟨ψ, rayleighNumerator ψ h, hn, hamiltonian_graph_formValue hg, ?_⟩
  rwa [formGroundEnergy_eq_variationalGroundEnergy]

/-- Zero belongs to the actual continuum spectrum, while the actual
Hamiltonian kernel is trivial. This is stated directly without imposing an
unproved spectral-type classification. -/
theorem nonpositive_charge_zero_spectrum_trivial_kernel {N : ℕ} (hN : 0 < N)
    {Z : ℝ} (hZ : Z ≤ 0) :
    variationalGroundEnergy N Z = 0 ∧ formGroundEnergy N Z = 0 ∧
    (0 : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z) ∧
    ∀ ψ : SpinSpace N, hamiltonianGraph N Z ψ 0 → ψ = 0 :=
  ⟨variational_ground_energy_eq_zero_of_charge_nonpos N hZ,
    form_ground_energy_eq_zero_of_charge_nonpos N hZ,
    zero_mem_coulomb_spectrum_of_charge_nonpos N hZ,
    fun _ hg => no_nonzero_zero_energy_graph_of_charge_nonpos hN hZ hg⟩

#print axioms variational_ground_energy_eq_zero_of_charge_nonpos
#print axioms no_normalized_h1_minimizer_of_charge_nonpos
#print axioms no_normalized_h2_minimizer_of_charge_nonpos
#print axioms nonpositive_charge_zero_spectrum_trivial_kernel

end TheoremT.Continuum
