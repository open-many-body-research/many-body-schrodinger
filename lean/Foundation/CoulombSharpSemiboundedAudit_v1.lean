import CoulombSharpSemibounded_v1

/-! Exact sharp-bound statement audit. The proof uses original weak tests,
the physical untruncated Coulomb multiplier, and no spectral input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
set_option pp.proofs false
set_option pp.maxSteps 100000

namespace TheoremT.Continuum.SharpBoundAudit

theorem actual_scalar_h1_energy_bound (N : ℕ) (Z : ℝ)
    (f v : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))
    (d : (Fin N × Fin 3) →
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))
    (hd : ∀ k, ∀ φ : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ,
      ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ x • d k x) = -(∫ x, (fderiv ℝ φ x (PiLp.single 2 k 1)) • f x))
    (hv : v =ᵐ[volume] fun x =>
      ((-Z * (∑ i : Fin N, ‖position x i‖⁻¹) +
        ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
          ‖position x i - position x j‖⁻¹ : ℝ) : ℂ) * f x) :
    -(N : ℝ) * (max Z 0)^2 / 2 * ‖f‖^2 ≤
      (1 / 2 : ℝ) * (∑ k : Fin N × Fin 3, ‖d k‖^2) + inner ℝ f v :=
  scalar_coulomb_h1_energy_sharp_bound Z f v d hd hv

theorem actual_h2_graph_lower_bound (N : ℕ) (Z : ℝ)
    (ψ h : PiLp 2 (fun _ : (Fin N → Fin 2) =>
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) )
    (hg : hamiltonianGraph N Z ψ h) :
    -(N : ℝ) * (max Z 0)^2 / 2 * ‖ψ‖^2 ≤ inner ℝ ψ h :=
  hamiltonian_graph_sharp_semibounded hg

theorem actual_normalized_energies_lower_bound (N : ℕ) (Z : ℝ) :
    (((-(N : ℝ) * (max Z 0)^2 / 2 : ℝ) : EReal) ≤ formGroundEnergy N Z) ∧
    (((-(N : ℝ) * (max Z 0)^2 / 2 : ℝ) : EReal) ≤ variationalGroundEnergy N Z) :=
  ⟨form_ground_energy_sharp_lower_bound N Z, variational_ground_energy_sharp_lower_bound N Z⟩

#print actual_scalar_h1_energy_bound
#print actual_h2_graph_lower_bound
#print actual_normalized_energies_lower_bound
#print TheoremT.Continuum.weak_nuclear_coulomb_bound
#print TheoremT.Continuum.coulombPotential_ge_attractive_part
#print axioms actual_scalar_h1_energy_bound
#print axioms actual_h2_graph_lower_bound
#print axioms actual_normalized_energies_lower_bound
#print axioms TheoremT.Continuum.weak_nuclear_coulomb_bound
#print axioms TheoremT.Continuum.coulombPotential_ge_attractive_part

end TheoremT.Continuum.SharpBoundAudit
