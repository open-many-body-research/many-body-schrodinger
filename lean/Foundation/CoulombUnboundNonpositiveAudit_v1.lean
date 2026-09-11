import CoulombUnboundNonpositive_v1

/-! Exact semantic audit of a continuum model whose spectral infimum is not
attained. N and the sign of Z are explicit, and no spectral type is assumed. -/
noncomputable section
open scoped LinearPMap
set_option pp.proofs false
set_option pp.maxSteps 100000

namespace TheoremT.Continuum.UnboundAudit

theorem actual_zero_bottom_nonattainment (N : ℕ) (hN : 0 < N)
    (Z : ℝ) (hZ : Z ≤ 0) :
    variationalGroundEnergy N Z = 0 ∧ formGroundEnergy N Z = 0 ∧
    (0 : ℂ) ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z) ∧
    (∀ z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator N Z),
      z.im = 0 ∧ 0 ≤ z.re) ∧
    (¬ ∃ ψ : SpinSpace N, ∃ q : ℝ, ‖ψ‖ = 1 ∧ coulombH1FormValue N Z ψ q ∧
      (q : EReal) = formGroundEnergy N Z) ∧
    (¬ ∃ ψ h : SpinSpace N, ‖ψ‖ = 1 ∧ hamiltonianGraph N Z ψ h ∧
      (rayleighNumerator ψ h : EReal) = variationalGroundEnergy N Z) ∧
    ∀ ψ : SpinSpace N, hamiltonianGraph N Z ψ 0 → ψ = 0 :=
  ⟨variational_ground_energy_eq_zero_of_charge_nonpos N hZ,
    form_ground_energy_eq_zero_of_charge_nonpos N hZ,
    zero_mem_coulomb_spectrum_of_charge_nonpos N hZ,
    fun _ hz => nonpositive_charge_spectrum_real_nonnegative N hZ hz,
    no_normalized_h1_minimizer_of_charge_nonpos hN hZ,
    no_normalized_h2_minimizer_of_charge_nonpos hN hZ,
    fun _ hg => no_nonzero_zero_energy_graph_of_charge_nonpos hN hZ hg⟩

#print actual_zero_bottom_nonattainment
#print TheoremT.Continuum.zero_isLeast_real_coulomb_spectrum_of_charge_nonpos
#print TheoremT.Continuum.variational_ground_energy_nonpositive
#print TheoremT.Continuum.coulombH1FormValue_pos_of_charge_nonpos
#print axioms actual_zero_bottom_nonattainment
#print axioms TheoremT.Continuum.zero_isLeast_real_coulomb_spectrum_of_charge_nonpos
#print axioms TheoremT.Continuum.variational_ground_energy_nonpositive
#print axioms TheoremT.Continuum.coulombH1FormValue_pos_of_charge_nonpos

end TheoremT.Continuum.UnboundAudit
