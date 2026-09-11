import TwoElectronComponentFormTransfer_v1

/-! The sum of the two actual hydrogenic component energies is at most the
unchanged Coulomb energy. The electron repulsion is nonnegative and retained
in the physical form; all singular expectations are integrable. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem twoElectron_scalar_components_le_energy (Z : ℝ) (hZ : 0 ≤ Z)
    (F v : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial F (d k) k)
    (hv : v =ᵐ[volume] fun x => (coulombPotential 2 Z x : ℂ) * F x) :
    twoElectronScalarComponentEnergy Z 0 F d + twoElectronScalarComponentEnergy Z 1 F d ≤
      (1/2 : ℝ) * (∑ k : Coordinate 2, ‖d k‖^2) + inner ℝ F v := by
  have hp := coulomb_expectation_ge_attractive_of_weakH1 Z F v d hd hv
  rw [max_eq_left hZ, Fin.sum_univ_two] at hp
  have hk : (∑ k : Coordinate 2, ‖d k‖^2) =
      (∑ k : Fin 3, ‖d (0,k)‖^2) + (∑ k : Fin 3, ‖d (1,k)‖^2) := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  rw [hk]
  unfold twoElectronScalarComponentEnergy
  linarith

#print axioms twoElectron_scalar_components_le_energy
end TheoremT.Continuum
