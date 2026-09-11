import HydrogenWeak_v1
import CoulombAttractiveExpectation_v1
import CoulombH1GraphEnergy_v1

/-! The sharp elementary nuclear lower bound for the genuine continuum
Coulomb form and Hamiltonian graph. The proof completes nuclear squares and
discards only the nonnegative electron repulsion; no hydrogen spectrum,
binding, eigenvector, or self-adjointness premise is imported. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem scalar_coulomb_h1_energy_sharp_bound {N : ℕ} (Z : ℝ)
    (f v : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    -(N : ℝ) * (max Z 0)^2 / 2 * ‖f‖^2 ≤
      (1 / 2 : ℝ) * (∑ k, ‖d k‖^2) + inner ℝ f v := by
  let t : ℝ := max Z 0
  have ht : 0 ≤ t := le_max_right Z 0
  have hsum : 2*t*(∑ i : Fin N, ∫ x, ‖f x‖^2 / ‖position x i‖) ≤
      (∑ k : Coordinate N, ‖d k‖^2) + (N : ℝ)*t^2*‖f‖^2 := by
    calc
      _ = ∑ i : Fin N, 2*t*(∫ x, ‖f x‖^2 / ‖position x i‖) := by rw [Finset.mul_sum]
      _ ≤ ∑ i : Fin N, ((∑ k : Fin 3, ‖d (i,k)‖^2) + t^2*‖f‖^2) :=
        Finset.sum_le_sum (fun i _ => (weak_nuclear_coulomb_bound i ht f d hd).2)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
          Fintype.card_fin, nsmul_eq_mul, Fintype.sum_prod_type]
        ring
  have hV := coulomb_expectation_ge_attractive_of_weakH1 Z f v d hd hv
  change -t * (∑ i : Fin N, ∫ x, ‖f x‖^2 / ‖position x i‖) ≤ inner ℝ f v at hV
  change -(N : ℝ)*t^2/2*‖f‖^2 ≤ _
  nlinarith

theorem scalar_graph_sharp_semibounded {N : ℕ} {Z : ℝ} {f h : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f h) :
    -(N : ℝ) * (max Z 0)^2 / 2 * ‖f‖^2 ≤ inner ℝ f h := by
  obtain ⟨d, hd⟩ := h2_implies_h1 (scalar_graph_hasH2 hg)
  have hm := coulombProductL2_of_hasH1 Z ⟨d, hd⟩
  let v : SpatialL2 N := hm.toLp _
  have hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x := hm.coeFn_toLp
  rw [scalar_graph_energy_identity hg d hd hv]
  exact scalar_coulomb_h1_energy_sharp_bound Z f v d hd hv

theorem coulombH1Energy_sharp_semibounded {N : ℕ} (Z : ℝ)
    (ψ : SpinSpace N) (d : Coordinate N → SpinSpace N) (v : SpinSpace N)
    (hd : ∀ σ k, WeakPartial (ψ σ) (d k σ) k)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    -(N : ℝ) * (max Z 0)^2 / 2 * ‖ψ‖^2 ≤ coulombH1Energy ψ d v := by
  simp only [coulombH1Energy, PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
  rw [Finset.sum_comm, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun σ _ =>
    scalar_coulomb_h1_energy_sharp_bound Z (ψ σ) (v σ) (fun k => d k σ) (hd σ) (hv σ))

theorem coulombH1FormValue_sharp_semibounded {N : ℕ} {Z : ℝ}
    {ψ : SpinSpace N} {q : ℝ} (hq : coulombH1FormValue N Z ψ q) :
    -(N : ℝ) * (max Z 0)^2 / 2 * ‖ψ‖^2 ≤ q := by
  obtain ⟨_, d, v, hd, hv, rfl⟩ := hq
  exact coulombH1Energy_sharp_semibounded Z ψ d v hd hv

theorem hamiltonian_graph_sharp_semibounded {N : ℕ} {Z : ℝ} {ψ h : SpinSpace N}
    (hg : hamiltonianGraph N Z ψ h) :
    -(N : ℝ) * (max Z 0)^2 / 2 * ‖ψ‖^2 ≤ inner ℝ ψ h := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.inner_apply, Finset.mul_sum]
  exact Finset.sum_le_sum (fun σ _ => scalar_graph_sharp_semibounded (hg.2.2 σ))

theorem variational_ground_energy_sharp_lower_bound (N : ℕ) (Z : ℝ) :
    ((-(N : ℝ) * (max Z 0)^2 / 2 : ℝ) : EReal) ≤ variationalGroundEnergy N Z := by
  apply le_sInf
  rintro E ⟨ψ, h, hn, hg, rfl⟩
  have hb := hamiltonian_graph_sharp_semibounded hg
  rw [hn, one_pow, mul_one, ← rayleighNumerator_eq_real_inner] at hb
  exact_mod_cast hb

theorem form_ground_energy_sharp_lower_bound (N : ℕ) (Z : ℝ) :
    ((-(N : ℝ) * (max Z 0)^2 / 2 : ℝ) : EReal) ≤ formGroundEnergy N Z := by
  apply le_sInf
  rintro E ⟨ψ, q, hn, hq, rfl⟩
  have hb := coulombH1FormValue_sharp_semibounded hq
  rw [hn, one_pow, mul_one] at hb
  exact_mod_cast hb

#print axioms scalar_coulomb_h1_energy_sharp_bound
#print axioms scalar_graph_sharp_semibounded
#print axioms coulombH1FormValue_sharp_semibounded
#print axioms hamiltonian_graph_sharp_semibounded
#print axioms variational_ground_energy_sharp_lower_bound
#print axioms form_ground_energy_sharp_lower_bound

end TheoremT.Continuum
