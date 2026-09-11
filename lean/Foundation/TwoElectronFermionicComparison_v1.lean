import TwoElectronFermionicJointProjection_v1

/-! The comparison algebra on the actual fermionic space, after constructing its maps.
The two physical hydrogenic form estimates remain explicit analytic obligations. -/
noncomputable section
namespace TheoremT.Continuum

theorem twoElectron_fermionic_comparison_of_component_bounds
    (f : SpatialL2 1) (hf : ‖f‖=1) (ψ : FermionicSpace 2) (Z e1 e2 e : ℝ)
    (h1 : -(Z^2/8) * ‖ψ.val‖^2 -
      (3*Z^2/8) * ‖twoElectronSpinProjectFirst f ψ.val‖^2 ≤ e1)
    (h2 : -(Z^2/8) * ‖ψ.val‖^2 -
      (3*Z^2/8) * ‖twoElectronSpinProjectSecond f ψ.val‖^2 ≤ e2)
    (he : e1+e2 ≤ e) :
    -(5*Z^2/8) * ‖ψ‖^2 ≤
      e + (3*Z^2/8) * ‖inner ℂ (twoElectronFermionicSinglet f) ψ‖^2 := by
  have h := OperatorTheory.two_hydrogenic_comparisons_combine
    (twoElectronSpinProjectFirst f).toLinearMap (twoElectronSpinProjectSecond f).toLinearMap
    (twoElectronSpinProjectFirst_isSymmetricProjection f hf)
    (twoElectronSpinProjectSecond_isSymmetricProjection f hf)
    (twoElectronSpinProject_commute f f) ψ.val Z e1 e2 e h1 h2 he
  change -(5*Z^2/8) * ‖ψ.val‖^2 ≤ e + (3*Z^2/8) *
    ‖twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ.val)‖^2 at h
  rw [twoElectron_fermionic_joint_norm_sq f hf ψ.property] at h
  exact h

theorem twoElectron_fermionic_complement_of_component_bounds
    (f : SpatialL2 1) (hf : ‖f‖=1) (ψ : FermionicSpace 2) (Z e1 e2 e : ℝ)
    (h1 : -(Z^2/8) * ‖ψ.val‖^2 -
      (3*Z^2/8) * ‖twoElectronSpinProjectFirst f ψ.val‖^2 ≤ e1)
    (h2 : -(Z^2/8) * ‖ψ.val‖^2 -
      (3*Z^2/8) * ‖twoElectronSpinProjectSecond f ψ.val‖^2 ≤ e2)
    (he : e1+e2 ≤ e) (horth : inner ℂ (twoElectronFermionicSinglet f) ψ = 0) :
    -(5*Z^2/8) * ‖ψ‖^2 ≤ e := by
  have h := twoElectron_fermionic_comparison_of_component_bounds f hf ψ Z e1 e2 e h1 h2 he
  simpa only [horth,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] using h

#print axioms twoElectron_fermionic_comparison_of_component_bounds
#print axioms twoElectron_fermionic_complement_of_component_bounds
end TheoremT.Continuum
