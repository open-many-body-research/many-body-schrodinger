import CoulombH1Form_v1

/-! Literal integral interpretation of the H¹ form, including integrability
of the untruncated physical potential energy density. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem complex_real_inner_mul_self (c : ℝ) (z : ℂ) :
    inner ℝ z ((c : ℂ) * z) = c * ‖z‖^2 := by
  rw [← Complex.real_smul, inner_smul_right, real_inner_self_eq_norm_sq]

theorem coulomb_potential_energy_integrable {N : ℕ} {Z : ℝ} {f v : SpatialL2 N}
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    Integrable (fun x => coulombPotential N Z x * ‖f x‖^2) := by
  apply (L2.integrable_inner (𝕜 := ℝ) f v).congr
  filter_upwards [hv] with x hx
  rw [hx, complex_real_inner_mul_self]

theorem coulomb_potential_energy_eq_integral {N : ℕ} {Z : ℝ} {f v : SpatialL2 N}
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    inner ℝ f v = ∫ x, coulombPotential N Z x * ‖f x‖^2 := by
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hv] with x hx
  rw [hx, complex_real_inner_mul_self]

theorem coulombH1Energy_eq_physical_integrals {N : ℕ} {Z : ℝ}
    (ψ : SpinSpace N) (d : Coordinate N → SpinSpace N) (v : SpinSpace N)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    coulombH1Energy ψ d v =
      (1 / 2 : ℝ) * (∑ k, ∑ σ : SpinConfiguration N, ‖d k σ‖^2) +
        ∑ σ : SpinConfiguration N, ∫ x, coulombPotential N Z x * ‖ψ σ x‖^2 := by
  simp only [coulombH1Energy, PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
  congr 1
  exact Finset.sum_congr rfl (fun σ _ => coulomb_potential_energy_eq_integral (hv σ))

#print axioms coulomb_potential_energy_integrable
#print axioms coulombH1Energy_eq_physical_integrals

end TheoremT.Continuum
