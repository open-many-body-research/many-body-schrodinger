import TwoElectronHydrogenComponents_v1
import TwoElectronAttractiveForm_v1

/-! Actual two-electron Coulomb rank-one comparison on the full fermionic
weak-H1 space. All physical component, spin, slicing, and repulsion estimates
are proved. This form comparison alone does not assert ground attainment. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum
open TheoremT.Polar

theorem twoElectron_spin_components_le_energy (Z : ℝ) (hZ : 0 ≤ Z)
    (ψ v : SpinSpace 2) (d : Coordinate 2 → SpinSpace 2)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential 2 Z x : ℂ) * ψ σ x) :
    twoElectronSpinComponentEnergy Z 0 ψ d + twoElectronSpinComponentEnergy Z 1 ψ d ≤
      coulombH1Energy ψ d v := by
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun σ _ =>
    twoElectron_scalar_components_le_energy Z hZ (ψ σ) (v σ) (fun k => d k σ) (hd σ) (hv σ))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  have hk : (∑ σ : SpinConfiguration 2, ∑ k : Coordinate 2, ‖d k σ‖^2) =
      ∑ k : Coordinate 2, ∑ σ : SpinConfiguration 2, ‖d k σ‖^2 := Finset.sum_comm
  rw [hk] at hs
  simpa only [twoElectronSpinComponentEnergy, coulombH1Energy,
    PiLp.norm_sq_eq_of_L2, PiLp.inner_apply] using hs

theorem twoElectron_physical_rank_one (Z : ℝ) (hZ : 0 < Z)
    (ψ : FermionicSpace 2) (v : SpinSpace 2) (d : Coordinate 2 → SpinSpace 2)
    (hd : ∀ σ k, WeakPartial (ψ.val σ) (d k σ) k)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential 2 Z x : ℂ) * ψ.val σ x) :
    -(5*Z^2/8) * ‖ψ‖^2 ≤ coulombH1Energy ψ.val d v + (3*Z^2/8) *
      ‖inner ℂ (twoElectronFermionicSinglet
        (normalizedPolarGround configuration_one_finrank Z hZ)) ψ‖^2 := by
  exact twoElectron_fermionic_comparison_of_component_bounds
    (normalizedPolarGround configuration_one_finrank Z hZ)
    (normalizedPolarGround_norm configuration_one_finrank Z hZ) ψ Z _ _ _
    (twoElectron_first_spin_hydrogen_component Z hZ ψ.val d hd)
    (twoElectron_second_spin_hydrogen_component Z hZ ψ.val d hd)
    (twoElectron_spin_components_le_energy Z hZ.le ψ.val v d hd hv)

theorem twoElectron_h1_form_rank_one (Z : ℝ) (hZ : 0 < Z)
    (ψ : FermionicSpace 2) (q : ℝ) (hq : coulombH1FormValue 2 Z ψ.val q) :
    -(5*Z^2/8) * ‖ψ‖^2 ≤ q + (3*Z^2/8) *
      ‖inner ℂ (twoElectronFermionicSinglet
        (normalizedPolarGround configuration_one_finrank Z hZ)) ψ‖^2 := by
  obtain ⟨_,d,v,hd,hv,rfl⟩ := hq
  exact twoElectron_physical_rank_one Z hZ ψ v d hd hv

#print axioms twoElectron_spin_components_le_energy
#print axioms twoElectron_physical_rank_one
#print axioms twoElectron_h1_form_rank_one
end TheoremT.Continuum
