import CoulombRelativeBound_v2

/-! Explicit semiboundedness on the actual weak continuum Coulomb graph.
The constant is coarse and makes no use of repulsive positivity or antisymmetry.
The variational lower bound is not an identification with the spectrum. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem scalar_graph_semibounded {N : ℕ} {Z : ℝ} {f h : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f h) :
    -(2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))^2 / 2 * ‖f‖^2 ≤ inner ℝ f h := by
  obtain ⟨d, e, hd, he, hout⟩ := hg
  let Δ : SpatialL2 N := ∑ k : Coordinate N, e k k
  let v : SpatialL2 N := h - (-((1 : ℝ) / 2)) • Δ
  have hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x := by
    filter_upwards [hout, Lp.coeFn_sub h (-((1 : ℝ) / 2) • Δ),
      Lp.coeFn_smul (-((1 : ℝ) / 2)) Δ,
      Lp.coeFn_fun_finsetSum Finset.univ (fun k => e k k)] with x hx hvx hcx hΔx
    dsimp only [v]
    simp only [Pi.sub_apply, Pi.smul_apply] at hvx hcx
    rw [hvx, hcx, hΔx, hx]
    simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  let D : ℝ := ∑ k : Coordinate N, ‖d k‖^2
  let C : ℝ := 2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ))
  have hD : 0 ≤ D := Finset.sum_nonneg (fun k _ => sq_nonneg ‖d k‖)
  have hE : D = -inner ℝ f Δ := weak_laplacian_energy_identity d (fun k => e k k) hd
    (fun k => he k k)
  have hV : ‖v‖ ≤ C * Real.sqrt D := coulomb_product_norm_le Z f d hd v hv
  have hinner : -(‖f‖ * ‖v‖) ≤ inner ℝ f v :=
    neg_le_of_abs_le (abs_real_inner_le_norm f v)
  have hnorm := mul_le_mul_of_nonneg_left hV (norm_nonneg f)
  have hquad := sq_nonneg (Real.sqrt D - C * ‖f‖)
  simp only [sub_sq, mul_pow, Real.sq_sqrt hD] at hquad
  have hdecomp : h = v + (-((1 : ℝ) / 2)) • Δ := (sub_add_cancel h _).symm
  rw [hdecomp, inner_add_right, inner_smul_right]
  change -C^2 / 2 * ‖f‖^2 ≤ _
  nlinarith

theorem hamiltonian_graph_semibounded {N : ℕ} {Z : ℝ} {ψ h : SpinSpace N}
    (hg : hamiltonianGraph N Z ψ h) :
    -(2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))^2 / 2 * ‖ψ‖^2 ≤ inner ℝ ψ h := by
  rw [PiLp.norm_sq_eq_of_L2, PiLp.inner_apply, Finset.mul_sum]
  exact Finset.sum_le_sum (fun σ _ => scalar_graph_semibounded (hg.2.2 σ))

theorem rayleighNumerator_eq_real_inner {N : ℕ} (ψ h : SpinSpace N) :
    rayleighNumerator ψ h = inner ℝ ψ h := by
  simp only [rayleighNumerator, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro σ _
  rw [L2.inner_def, L2.inner_def]
  have hr := (Complex.reCLM.integral_comp_comm
    (L2.integrable_inner (𝕜 := ℂ) (ψ σ) (h σ))).symm
  change (∫ x, inner ℂ (ψ σ x) (h σ x)).re =
    (∫ x, (inner ℂ (ψ σ x) (h σ x)).re) at hr
  exact hr

/-- A finite lower bound for the original extended-real variational infimum.
It does not assert nonemptiness, attainment, or a spectral interpretation. -/
theorem variational_ground_energy_lower_bound (N : ℕ) (Z : ℝ) :
    ((-(2 * (|Z| * (N : ℝ) + (N.choose 2 : ℝ)))^2 / 2 : ℝ) : EReal) ≤
      variationalGroundEnergy N Z := by
  apply le_sInf
  rintro E ⟨ψ, h, hn, hg, rfl⟩
  have hb := hamiltonian_graph_semibounded hg
  rw [hn, one_pow, mul_one, ← rayleighNumerator_eq_real_inner] at hb
  exact_mod_cast hb

#print axioms scalar_graph_semibounded
#print axioms hamiltonian_graph_semibounded
#print axioms rayleighNumerator_eq_real_inner
#print axioms variational_ground_energy_lower_bound

end TheoremT.Continuum
