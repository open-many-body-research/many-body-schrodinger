import CoulombH1Form_v1

/-! Exact agreement between the actual H¹ Coulomb form and the original weak
H² Hamiltonian graph. This identifies form values, not spectral points. -/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem scalar_graph_energy_identity {N : ℕ} {Z : ℝ} {f h v : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f h) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    inner ℝ f h = (1 / 2 : ℝ) * (∑ k, ‖d k‖^2) + inner ℝ f v := by
  obtain ⟨d', e, hd', he, hout⟩ := hg
  have hdd : d' = d := funext (fun k => weakPartial_unique (hd' k) (hd k))
  subst d'
  let Δ : SpatialL2 N := ∑ k : Coordinate N, e k k
  let w : SpatialL2 N := h - (-((1 : ℝ) / 2)) • Δ
  have hw : w =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x := by
    filter_upwards [hout, Lp.coeFn_sub h (-((1 : ℝ) / 2) • Δ),
      Lp.coeFn_smul (-((1 : ℝ) / 2)) Δ,
      Lp.coeFn_fun_finsetSum Finset.univ (fun k => e k k)] with x hx hwx hcx hΔx
    dsimp only [w]
    simp only [Pi.sub_apply, Pi.smul_apply] at hwx hcx
    rw [hwx, hcx, hΔx, hx]
    simp only [Complex.real_smul, Complex.ofReal_neg, Complex.ofReal_div,
      Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  have hwv : w = v := Lp.ext (hw.trans hv.symm)
  have hE : (∑ k : Coordinate N, ‖d k‖^2) = -inner ℝ f Δ :=
    weak_laplacian_energy_identity d (fun k => e k k) hd (fun k => he k k)
  have hdecomp : h = v + (-((1 : ℝ) / 2)) • Δ := by
    rw [← hwv]
    exact (sub_add_cancel h _).symm
  rw [hdecomp, inner_add_right, inner_smul_right, hE]
  ring

theorem coulombH1FormValue_eq_graph_energy {N : ℕ} {Z : ℝ}
    {ψ h : SpinSpace N} {q : ℝ}
    (hq : coulombH1FormValue N Z ψ q) (hg : hamiltonianGraph N Z ψ h) :
    q = rayleighNumerator ψ h := by
  obtain ⟨_, d, v, hd, hv, rfl⟩ := hq
  rw [rayleighNumerator_eq_real_inner]
  simp only [coulombH1Energy, PiLp.norm_sq_eq_of_L2, PiLp.inner_apply]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro σ _
  exact (scalar_graph_energy_identity (hg.2.2 σ) (fun k => d k σ) (hd σ) (hv σ)).symm

theorem hamiltonian_graph_formValue {N : ℕ} {Z : ℝ} {ψ h : SpinSpace N}
    (hg : hamiltonianGraph N Z ψ h) :
    coulombH1FormValue N Z ψ (rayleighNumerator ψ h) := by
  have hdom : ψ ∈ h1TargetDomain N :=
    ⟨hg.1, fun σ => h2_implies_h1 (scalar_graph_hasH2 (hg.2.2 σ))⟩
  obtain ⟨q, hq⟩ := (coulombH1FormValue_exists_iff Z ψ).mpr hdom
  rw [← coulombH1FormValue_eq_graph_energy hq hg]
  exact hq

theorem form_ground_le_variational (N : ℕ) (Z : ℝ) :
    formGroundEnergy N Z ≤ variationalGroundEnergy N Z := by
  apply le_sInf
  rintro E ⟨ψ, h, hn, hg, rfl⟩
  exact sInf_le ⟨ψ, rayleighNumerator ψ h, hn, hamiltonian_graph_formValue hg, rfl⟩

#print axioms coulombH1FormValue_eq_graph_energy
#print axioms hamiltonian_graph_formValue
#print axioms form_ground_le_variational

end TheoremT.Continuum
