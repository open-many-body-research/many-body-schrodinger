import CoulombExponentialDecay_v1
import TwoElectronExteriorCoercivity_v1
import TwoElectronGroundRotation_v1

/-! Actual two-electron ground eigenfunction decay for every real Z >= 2.
The energy is the previously identified actual full fermionic spectral bottom.
The exterior-coercivity premise of the general decay theorem is discharged.
No quantitative prefactor or computable radius is claimed here. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem twoElectron_ground_exponential_decay (Z : ℝ) (hZ : 2 ≤ Z)
    {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f
      (((variationalGroundEnergy 2 Z).toReal : ℂ) • f))
    {a : ℝ} (ha : 0 ≤ a) (hgap : a^2 < Z^2/112) :
    MemLp (fun x => Real.exp (a*‖x‖) • f x) 2 volume := by
  obtain ⟨R,hR,hcoerc⟩ := twoElectron_exterior_coercivity Z hZ
  exact scalar_eigen_exponential_decay_of_exterior_coercivity hg hR ha hgap hcoerc

theorem twoElectron_ground_decay_charge_sixteenth (Z : ℝ) (hZ : 2 ≤ Z)
    {f : SpatialL2 2}
    (hg : scalarHamiltonianGraph 2 Z f
      (((variationalGroundEnergy 2 Z).toReal : ℂ) • f)) :
    MemLp (fun x => Real.exp ((Z/16)*‖x‖) • f x) 2 volume := by
  apply twoElectron_ground_exponential_decay Z hZ hg (by positivity)
  have hp : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  nlinarith [sq_pos_of_pos hp]

theorem twoElectron_ground_real_symmetric_rotation_decay (Z : ℝ) (hZ : 2 ≤ Z) :
    ∃ u : SpatialL2 2, ‖u‖ = 1 ∧ pullback twoElectronSwap u = u ∧ HasH2 u ∧
      scalarHamiltonianGraph 2 Z u (((variationalGroundEnergy 2 Z).toReal : ℂ) • u) ∧
      (∀ᵐ x, (u x).im = 0) ∧
      (∀ R : Position ≃ₗᵢ[ℝ] Position, spatialRotation 2 R u = u) ∧
      ∀ a : ℝ, 0 ≤ a → a^2 < Z^2/112 →
        MemLp (fun x => Real.exp (a*‖x‖) • u x) 2 volume := by
  have hp : 0 < Z := lt_of_lt_of_le (by norm_num) hZ
  have hsep : 32 < 9*Z^2 := by nlinarith [sq_nonneg (Z-2)]
  obtain ⟨u,hu,hs,hH2,hg,hr,hrot⟩ := twoElectron_ground_real_rotation_invariant Z hp hsep
  exact ⟨u,hu,hs,hH2,hg,hr,hrot,fun a ha hgap =>
    twoElectron_ground_exponential_decay Z hZ hg ha hgap⟩

#print axioms twoElectron_ground_exponential_decay
#print axioms twoElectron_ground_decay_charge_sixteenth
#print axioms twoElectron_ground_real_symmetric_rotation_decay
end TheoremT.Continuum
