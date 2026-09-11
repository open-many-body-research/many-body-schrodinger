import TwoElectronComponentFormTransfer_v1
import TwoElectronFermionicComparison_v1
import HydrogenWeakH1Comparison_v1

/-! Actual two-electron hydrogen component bounds, including full spin sum.
The one-electron inequality and Sobolev slicing are discharged, not premises. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum
open TheoremT.Polar

def twoElectronSpinComponentEnergy (Z : ℝ) (i : Fin 2) (ψ : SpinSpace 2)
    (d : Coordinate 2 → SpinSpace 2) : ℝ :=
  ∑ σ : SpinConfiguration 2, twoElectronScalarComponentEnergy Z i (ψ σ) (fun k => d k σ)

theorem twoElectron_first_hydrogen_component (Z : ℝ) (hZ : 0 < Z)
    (F : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial F (d k) k) :
    -(Z^2/8) * ‖F‖^2 ≤ twoElectronScalarComponentEnergy Z 0 F d +
      (3*Z^2/8) * ‖twoElectronProjectFirst
        (normalizedPolarGround configuration_one_finrank Z hZ) F‖^2 :=
  twoElectron_first_component_of_oneElectron_bound _
    (normalizedPolarGround_norm configuration_one_finrank Z hZ) Z (-(Z^2/8)) (3*Z^2/8)
    (hydrogen_weakH1_rank_one Z hZ) F d hd

theorem twoElectron_second_hydrogen_component (Z : ℝ) (hZ : 0 < Z)
    (F : SpatialL2 2) (d : Coordinate 2 → SpatialL2 2)
    (hd : ∀ k, WeakPartial F (d k) k) :
    -(Z^2/8) * ‖F‖^2 ≤ twoElectronScalarComponentEnergy Z 1 F d +
      (3*Z^2/8) * ‖twoElectronProjectSecond
        (normalizedPolarGround configuration_one_finrank Z hZ) F‖^2 :=
  twoElectron_second_component_of_oneElectron_bound _
    (normalizedPolarGround_norm configuration_one_finrank Z hZ) Z (-(Z^2/8)) (3*Z^2/8)
    (hydrogen_weakH1_rank_one Z hZ) F d hd

theorem twoElectron_first_spin_hydrogen_component (Z : ℝ) (hZ : 0 < Z)
    (ψ : SpinSpace 2) (d : Coordinate 2 → SpinSpace 2)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k) :
    -(Z^2/8) * ‖ψ‖^2 - (3*Z^2/8) *
      ‖twoElectronSpinProjectFirst (normalizedPolarGround configuration_one_finrank Z hZ) ψ‖^2 ≤
      twoElectronSpinComponentEnergy Z 0 ψ d := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun σ _ => twoElectron_first_hydrogen_component Z hZ (ψ σ) (fun k => d k σ) (hd σ))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [twoElectronSpinProjectFirst_apply, twoElectronSpinComponentEnergy]
  linarith

theorem twoElectron_second_spin_hydrogen_component (Z : ℝ) (hZ : 0 < Z)
    (ψ : SpinSpace 2) (d : Coordinate 2 → SpinSpace 2)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k) :
    -(Z^2/8) * ‖ψ‖^2 - (3*Z^2/8) *
      ‖twoElectronSpinProjectSecond (normalizedPolarGround configuration_one_finrank Z hZ) ψ‖^2 ≤
      twoElectronSpinComponentEnergy Z 1 ψ d := by
  have h := Finset.sum_le_sum (s := Finset.univ)
    (fun σ _ => twoElectron_second_hydrogen_component Z hZ (ψ σ) (fun k => d k σ) (hd σ))
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
  rw [PiLp.norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2]
  simp only [twoElectronSpinProjectSecond_apply, twoElectronSpinComponentEnergy]
  linarith

#print axioms twoElectron_first_hydrogen_component
#print axioms twoElectron_second_hydrogen_component
#print axioms twoElectron_first_spin_hydrogen_component
#print axioms twoElectron_second_spin_hydrogen_component
end TheoremT.Continuum
