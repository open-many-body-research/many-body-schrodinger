import CoulombSharpSemibounded_v1

/-! Positive form energy for every nonzero actual H¹ vector when N>0 and Z≤0.
This proves the nonattainment ingredient independently of any spectral or
dilation upper-bound argument. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace TheoremT.Continuum

theorem weakH1_eq_zero_of_gradient_energy_zero {N : ℕ} (i : Fin N)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) (hD : (∑ k, ‖d k‖^2) = 0) : f = 0 := by
  let hm := (weak_nuclear_memLp_two_and_bound i f d hd).1
  have hb := nuclear_product_norm_le i f d hd
  have hz : hm.toLp (fun x => f x / (‖position x i‖ : ℂ)) = 0 := by
    apply norm_le_zero_iff.mp
    simpa only [hD, Real.sqrt_zero, mul_zero] using hb
  apply Lp.ext
  filter_upwards [hm.coeFn_toLp, Lp.coeFn_zero ℂ 2 (volume : Measure (Configuration N)),
    ae_collisionFree N] with x hx hzx hcx
  rw [hz, hzx] at hx
  have hr : (‖position x i‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (hcx.1 i))
  have hf := (div_eq_iff hr).mp hx.symm
  simpa only [Pi.zero_apply, zero_mul, hzx] using hf

theorem scalar_coulomb_h1_energy_pos_of_charge_nonpos {N : ℕ}
    (i : Fin N) {Z : ℝ} (hZ : Z ≤ 0) (f v : SpatialL2 N)
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x)
    (hf : f ≠ 0) :
    0 < (1 / 2 : ℝ) * (∑ k, ‖d k‖^2) + inner ℝ f v := by
  have hD : 0 < ∑ k, ‖d k‖^2 := by
    have hnn : 0 ≤ ∑ k, ‖d k‖^2 := Finset.sum_nonneg (fun k _ => sq_nonneg _)
    by_contra hn
    have hz := le_antisymm (not_lt.mp hn) hnn
    exact hf (weakH1_eq_zero_of_gradient_energy_zero i f d hd hz)
  have hV : 0 ≤ inner ℝ f v := by
    simpa only [max_eq_right hZ, neg_zero, zero_mul] using
      coulomb_expectation_ge_attractive_of_weakH1 Z f v d hd hv
  nlinarith

theorem coulombH1FormValue_pos_of_charge_nonpos {N : ℕ} (hN : 0 < N)
    {Z : ℝ} (hZ : Z ≤ 0) {ψ : SpinSpace N} {q : ℝ}
    (hq : coulombH1FormValue N Z ψ q) (hψ : ψ ≠ 0) : 0 < q := by
  obtain ⟨_, d, v, hd, hv, rfl⟩ := hq
  have hσ : ∃ σ : SpinConfiguration N, ψ σ ≠ 0 := by
    by_contra h
    apply hψ
    apply (WithLp.ext_iff 2).mpr
    funext σ
    exact not_not.mp (not_exists.mp h σ)
  obtain ⟨σ₀, hσ₀⟩ := hσ
  have hnonneg (σ : SpinConfiguration N) :
      0 ≤ (1 / 2 : ℝ) * (∑ k, ‖d k σ‖^2) + inner ℝ (ψ σ) (v σ) := by
    simpa only [max_eq_right hZ, zero_pow (by norm_num : 2 ≠ 0),
      mul_zero, zero_div, zero_mul] using
      scalar_coulomb_h1_energy_sharp_bound Z (ψ σ) (v σ) (fun k => d k σ) (hd σ) (hv σ)
  have hpos := scalar_coulomb_h1_energy_pos_of_charge_nonpos
    (⟨0,hN⟩ : Fin N) hZ (ψ σ₀) (v σ₀) (fun k => d k σ₀) (hd σ₀) (hv σ₀) hσ₀
  simp only [coulombH1Energy, PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_pos' (fun σ _ => hnonneg σ) ⟨σ₀, Finset.mem_univ σ₀, hpos⟩

theorem hamiltonian_graph_energy_pos_of_charge_nonpos {N : ℕ} (hN : 0 < N)
    {Z : ℝ} (hZ : Z ≤ 0) {ψ h : SpinSpace N}
    (hg : hamiltonianGraph N Z ψ h) (hψ : ψ ≠ 0) : 0 < rayleighNumerator ψ h :=
  coulombH1FormValue_pos_of_charge_nonpos hN hZ (hamiltonian_graph_formValue hg) hψ

theorem no_nonzero_zero_energy_graph_of_charge_nonpos {N : ℕ} (hN : 0 < N)
    {Z : ℝ} (hZ : Z ≤ 0) {ψ : SpinSpace N}
    (hg : hamiltonianGraph N Z ψ 0) : ψ = 0 := by
  by_contra hψ
  have hpos := hamiltonian_graph_energy_pos_of_charge_nonpos hN hZ hg hψ
  simpa [rayleighNumerator] using hpos

#print axioms weakH1_eq_zero_of_gradient_energy_zero
#print axioms coulombH1FormValue_pos_of_charge_nonpos
#print axioms no_nonzero_zero_energy_graph_of_charge_nonpos

end TheoremT.Continuum
