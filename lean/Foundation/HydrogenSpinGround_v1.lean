import HydrogenSpinStructure_v1
import HydrogenEigenGraph_v1
import EigenRayleighUpper_v1
import CoulombSpectralFoundation_v3

/-! The exact one-electron ground energy in the full physical fermionic spin
space, with an injective two-dimensional family of actual graph eigenvectors.
No uniqueness or upper bound on ground-state multiplicity is asserted. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem hydrogenSpinMap_eigenGraph (Z : ℝ) (hZ : 0 < Z) (c : Fin 2 → ℂ) :
    hamiltonianGraph 1 Z (hydrogenSpinMap Z hZ c)
      ((-(Z ^ 2 / 2) : ℂ) • hydrogenSpinMap Z hZ c) :=
  oneElectronSpinMap_eigen_graph (hydrogenRadialL2_eigenGraph Z hZ) c

theorem hydrogen_ground_energy (Z : ℝ) (hZ : 0 < Z) :
    variationalGroundEnergy 1 Z = ((-(Z ^ 2 / 2) : ℝ) : EReal) := by
  apply le_antisymm
  · have hc : (fun _ : Fin 2 => (1 : ℂ)) ≠ 0 := by
      intro h
      have hh := congrFun h 0
      simp at hh
    have hg := hydrogenSpinMap_eigenGraph Z hZ (fun _ => 1)
    have hg' : hamiltonianGraph 1 Z (hydrogenSpinMap Z hZ (fun _ => 1))
        (((-(Z ^ 2 / 2) : ℝ) : ℂ) • hydrogenSpinMap Z hZ (fun _ => 1)) := by
      simpa using hg
    exact variational_ground_le_graph_eigenvalue (hydrogenSpinMap_nonzero Z hZ hc) hg'
  · simpa [max_eq_left hZ.le, neg_div] using variational_ground_energy_sharp_lower_bound 1 Z

theorem hydrogen_form_ground_energy (Z : ℝ) (hZ : 0 < Z) :
    formGroundEnergy 1 Z = ((-(Z ^ 2 / 2) : ℝ) : EReal) := by
  rw [formGroundEnergy_eq_variationalGroundEnergy, hydrogen_ground_energy Z hZ]

theorem hydrogen_spectral_ground_energy (Z : ℝ) (hZ : 0 < Z) :
    spectralGroundEnergy 1 Z = ((-(Z ^ 2 / 2) : ℝ) : EReal) := by
  rw [spectralGroundEnergy_eq_variationalGroundEnergy, hydrogen_ground_energy Z hZ]

theorem hydrogen_ground_energy_mem_spectrum (Z : ℝ) (hZ : 0 < Z) :
    (-(Z ^ 2 / 2) : ℂ) ∈
      TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 1 Z) := by
  have h := coulomb_variational_energy_mem_spectrum 1 Z
  rw [hydrogen_ground_energy Z hZ] at h
  simpa using h

theorem hydrogen_spin_ground_eigenfamily (Z : ℝ) (hZ : 0 < Z) :
    LinearIndependent ℂ (fun j : Fin 2 => hydrogenSpinMap Z hZ (Pi.basisFun ℂ (Fin 2) j)) ∧
    ∀ j : Fin 2, hamiltonianGraph 1 Z
      (hydrogenSpinMap Z hZ (Pi.basisFun ℂ (Fin 2) j))
      ((-(Z ^ 2 / 2) : ℂ) • hydrogenSpinMap Z hZ (Pi.basisFun ℂ (Fin 2) j)) :=
  ⟨hydrogenSpinMap_two_independent Z hZ,
    fun j => hydrogenSpinMap_eigenGraph Z hZ (Pi.basisFun ℂ (Fin 2) j)⟩

theorem hydrogen_spectrum_lower_bound (Z : ℝ) (hZ : 0 < Z) {z : ℂ}
    (hz : z ∈ TheoremT.OperatorTheory.unboundedSpectrum (coulombPartialOperator 1 Z)) :
    -(Z ^ 2 / 2) ≤ z.re := by
  have h := coulomb_spectrum_re_lower_bound 1 Z hz
  rw [hydrogen_ground_energy Z hZ] at h
  simpa using h

/-- The physical spectral infimum and two independent actual ground
eigenvectors are established together, without an assumed eigenpair. -/
theorem hydrogen_full_spin_ground (Z : ℝ) (hZ : 0 < Z) :
    variationalGroundEnergy 1 Z = ((-(Z ^ 2 / 2) : ℝ) : EReal) ∧
    formGroundEnergy 1 Z = ((-(Z ^ 2 / 2) : ℝ) : EReal) ∧
    spectralGroundEnergy 1 Z = ((-(Z ^ 2 / 2) : ℝ) : EReal) ∧
    Function.Injective (hydrogenSpinMap Z hZ) ∧
    (∀ c : Fin 2 → ℂ, hydrogenSpinMap Z hZ c ∈ targetDomain 1 ∧
      hamiltonianGraph 1 Z (hydrogenSpinMap Z hZ c)
        ((-(Z ^ 2 / 2) : ℂ) • hydrogenSpinMap Z hZ c)) ∧
    LinearIndependent ℂ (fun j : Fin 2 => hydrogenSpinMap Z hZ (Pi.basisFun ℂ (Fin 2) j)) := by
  refine ⟨hydrogen_ground_energy Z hZ, hydrogen_form_ground_energy Z hZ,
    hydrogen_spectral_ground_energy Z hZ, hydrogenSpinMap_injective Z hZ, ?_,
    hydrogenSpinMap_two_independent Z hZ⟩
  intro c
  exact ⟨graph_input_in_targetDomain (hydrogenSpinMap_eigenGraph Z hZ c),
    hydrogenSpinMap_eigenGraph Z hZ c⟩

end TheoremT.Continuum
