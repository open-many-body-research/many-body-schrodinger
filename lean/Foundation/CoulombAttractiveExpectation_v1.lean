import CoulombH1PhysicalEnergy_v1

/-! The physical Coulomb potential and its expectation are bounded below by
the attractive nuclear part, for every real charge. No repulsion is changed
or truncated; only its pointwise nonnegativity is used. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum

theorem coulombPotential_ge_attractive_part (N : ℕ) (Z : ℝ)
    (x : Configuration N) :
    -(max Z 0) * (∑ i : Fin N, ‖position x i‖⁻¹) ≤ coulombPotential N Z x := by
  have hn : 0 ≤ ∑ i : Fin N, ‖position x i‖⁻¹ :=
    Finset.sum_nonneg (fun i _ => inv_nonneg.mpr (norm_nonneg _))
  have hp : 0 ≤ ∑ i : Fin N,
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
        ‖position x i - position x j‖⁻¹ := by
    apply Finset.sum_nonneg
    intro i _
    exact Finset.sum_nonneg (fun j _ => inv_nonneg.mpr (norm_nonneg _))
  calc
    _ ≤ -Z * (∑ i : Fin N, ‖position x i‖⁻¹) :=
      mul_le_mul_of_nonneg_right (neg_le_neg (le_max_left Z 0)) hn
    _ ≤ _ := le_add_of_nonneg_right hp

theorem complex_real_inner_div_self (r : ℝ) (z : ℂ) :
    inner ℝ z (z / (r : ℂ)) = ‖z‖^2 / r := by
  rw [div_eq_mul_inv, ← Complex.ofReal_inv, mul_comm z,
    complex_real_inner_mul_self]
  ring

theorem nuclear_potential_energy_integrable_of_weakH1 {N : ℕ}
    (i : Fin N) (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x => ‖f x‖^2 / ‖position x i‖) volume := by
  have hm := (weak_nuclear_memLp_two_and_bound i f d hd).1
  apply (L2.integrable_inner (𝕜 := ℝ) f (hm.toLp _)).congr
  filter_upwards [hm.coeFn_toLp] with x hx
  rw [hx, complex_real_inner_div_self]

theorem coulomb_expectation_ge_attractive_of_integrable {N : ℕ}
    (Z : ℝ) (f v : SpatialL2 N)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x)
    (hn : ∀ i : Fin N, Integrable (fun x => ‖f x‖^2 / ‖position x i‖) volume) :
    -(max Z 0) * (∑ i : Fin N, ∫ x, ‖f x‖^2 / ‖position x i‖) ≤
      inner ℝ f v := by
  have hs : Integrable (fun x => ∑ i : Fin N, ‖f x‖^2 / ‖position x i‖) volume :=
    integrable_finsetSum Finset.univ (fun i _ => hn i)
  have hsum (x : Configuration N) :
      (∑ i : Fin N, ‖f x‖^2 / ‖position x i‖) =
        (∑ i : Fin N, ‖position x i‖⁻¹) * ‖f x‖^2 := by
    simp only [Finset.sum_mul, div_eq_mul_inv, mul_comm]
  have hh := integral_mono (hs.const_mul (-(max Z 0)))
    (coulomb_potential_energy_integrable hv) (fun x => ?_)
  · rw [integral_const_mul, integral_finsetSum Finset.univ (fun i _ => hn i)] at hh
    rw [coulomb_potential_energy_eq_integral hv]
    exact hh
  · rw [hsum, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (coulombPotential_ge_attractive_part N Z x)
      (sq_nonneg ‖f x‖)

theorem coulomb_expectation_ge_attractive_of_weakH1 {N : ℕ}
    (Z : ℝ) (f v : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    -(max Z 0) * (∑ i : Fin N, ∫ x, ‖f x‖^2 / ‖position x i‖) ≤
      inner ℝ f v :=
  coulomb_expectation_ge_attractive_of_integrable Z f v hv
    (fun i => nuclear_potential_energy_integrable_of_weakH1 i f d hd)

#print axioms coulombPotential_ge_attractive_part
#print axioms nuclear_potential_energy_integrable_of_weakH1
#print axioms coulomb_expectation_ge_attractive_of_integrable
#print axioms coulomb_expectation_ge_attractive_of_weakH1

end TheoremT.Continuum
