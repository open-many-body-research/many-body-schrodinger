import CoulombAttractiveExpectation_v1

/-! Exact splitting of the untruncated two-electron potential expectation. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum

theorem pair_potential_energy_integrable_of_weakH1 {N : ℕ}
    (i j : Fin N) (hij : i ≠ j) (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x => ‖f x‖^2 / ‖position x i - position x j‖) volume := by
  have hm := (weak_pair_memLp_two_and_bound i j hij f d hd).1
  apply (L2.integrable_inner (𝕜 := ℝ) f (hm.toLp _)).congr
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx,complex_real_inner_div_self]

theorem coulombPotential_two_electrons (Z : ℝ) (q : Configuration 2) :
    coulombPotential 2 Z q = -Z * (‖position q 0‖⁻¹ + ‖position q 1‖⁻¹) +
      ‖position q 0 - position q 1‖⁻¹ := by
  simp [coulombPotential,Finset.sum_filter,Fin.sum_univ_two]

theorem twoElectron_potential_energy_decomposition (Z : ℝ) (f : SpatialL2 2)
    (d : Coordinate 2 → SpatialL2 2) (hd : ∀ k, WeakPartial f (d k) k) :
    (∫ q, coulombPotential 2 Z q * ‖f q‖^2) =
      -Z * (∫ q, ‖f q‖^2 / ‖position q 0‖) -
        Z * (∫ q, ‖f q‖^2 / ‖position q 1‖) +
          ∫ q, ‖f q‖^2 / ‖position q 0 - position q 1‖ := by
  have h0 := nuclear_potential_energy_integrable_of_weakH1 (0 : Fin 2) f d hd
  have h1 := nuclear_potential_energy_integrable_of_weakH1 (1 : Fin 2) f d hd
  have hp := pair_potential_energy_integrable_of_weakH1 (0 : Fin 2) 1 (by decide) f d hd
  have he : (fun q => coulombPotential 2 Z q * ‖f q‖^2) =
      (fun q => -Z * (‖f q‖^2 / ‖position q 0‖) -
        Z * (‖f q‖^2 / ‖position q 1‖) + ‖f q‖^2 / ‖position q 0 - position q 1‖) := by
    funext q
    rw [coulombPotential_two_electrons]
    ring
  have hs : Integrable (fun q => -Z * (‖f q‖^2 / ‖position q 0‖) -
      Z * (‖f q‖^2 / ‖position q 1‖)) := (h0.const_mul (-Z)).sub (h1.const_mul Z)
  have hsub := integral_sub (h0.const_mul (-Z)) (h1.const_mul Z)
  rw [he,integral_add hs hp,hsub,integral_const_mul,integral_const_mul]

#print axioms pair_potential_energy_integrable_of_weakH1
#print axioms coulombPotential_two_electrons
#print axioms twoElectron_potential_energy_decomposition
end TheoremT.Continuum
