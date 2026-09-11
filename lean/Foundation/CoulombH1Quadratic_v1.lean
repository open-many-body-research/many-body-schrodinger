import CoulombH1Continuity_v1

/-! Quadratic identities for the genuine fermionic weak-H¹ Coulomb form.
Complex scaling and addition/subtraction carry actual derivative and Coulomb
multiplication witnesses. No closed-form or spectral assertion is made. -/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum

theorem spin_coulomb_product_add {N : ℕ} {Z : ℝ} {ψ φ v w : SpinSpace N}
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x)
    (hw : ∀ σ, w σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * φ σ x) :
    ∀ σ, (v + w) σ =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * (ψ + φ) σ x := by
  intro σ
  change (v σ + w σ : SpatialL2 N) =ᵐ[volume]
    fun x => (coulombPotential N Z x : ℂ) * (ψ σ + φ σ : SpatialL2 N) x
  filter_upwards [hv σ, hw σ, Lp.coeFn_add (v σ) (w σ),
    Lp.coeFn_add (ψ σ) (φ σ)] with x hvx hwx hx hpx
  simp only [Pi.add_apply] at hx hpx
  rw [hx, hpx, hvx, hwx, mul_add]

theorem spin_coulomb_product_smul {N : ℕ} {Z : ℝ} {ψ v : SpinSpace N}
    (c : ℂ)
    (hv : ∀ σ, v σ =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * ψ σ x) :
    ∀ σ, (c • v) σ =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * (c • ψ) σ x := by
  intro σ
  change (c • v σ : SpatialL2 N) =ᵐ[volume]
    fun x => (coulombPotential N Z x : ℂ) * (c • ψ σ : SpatialL2 N) x
  filter_upwards [hv σ, Lp.coeFn_smul c (v σ), Lp.coeFn_smul c (ψ σ)]
    with x hvx hx hpx
  simp only [Pi.smul_apply, smul_eq_mul] at hx hpx
  rw [hx, hpx, hvx]
  ring

theorem spin_real_inner_smul_complex {N : ℕ} (c : ℂ) (ψ v : SpinSpace N) :
    inner ℝ (c • ψ) (c • v) = ‖c‖^2 * inner ℝ ψ v := by
  have hr (a b : SpinSpace N) : inner ℝ a b = (inner ℂ a b).re := by
    rw [← rayleighNumerator_eq_real_inner]
    simp only [rayleighNumerator, PiLp.inner_apply, Complex.re_sum]
  rw [hr, hr, inner_smul_left, inner_smul_right, ← mul_assoc]
  simp [RCLike.conj_mul, pow_two, Complex.mul_re]

theorem coulombH1Energy_smul {N : ℕ} (c : ℂ) (ψ : SpinSpace N)
    (d : Coordinate N → SpinSpace N) (v : SpinSpace N) :
    coulombH1Energy (c • ψ) (fun k => c • d k) (c • v) =
      ‖c‖^2 * coulombH1Energy ψ d v := by
  simp only [coulombH1Energy, norm_smul, mul_pow, ← Finset.mul_sum,
    spin_real_inner_smul_complex]
  ring

theorem coulombH1Energy_parallelogram {N : ℕ} (ψ φ : SpinSpace N)
    (d e : Coordinate N → SpinSpace N) (v w : SpinSpace N) :
    coulombH1Energy (ψ + φ) (fun k => d k + e k) (v + w) +
      coulombH1Energy (ψ - φ) (fun k => d k - e k) (v - w) =
        2 * coulombH1Energy ψ d v + 2 * coulombH1Energy φ e w := by
  have hk : (∑ k : Coordinate N, ‖d k + e k‖^2) +
      (∑ k : Coordinate N, ‖d k - e k‖^2) =
        2 * (∑ k, ‖d k‖^2) + 2 * (∑ k, ‖e k‖^2) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [parallelogram_law_with_norm ℂ]
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
    ring
  have hi : inner ℝ (ψ + φ) (v + w) + inner ℝ (ψ - φ) (v - w) =
      2 * inner ℝ ψ v + 2 * inner ℝ φ w := by
    simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
    ring
  unfold coulombH1Energy
  linarith

theorem coulombH1FormValue_smul {N : ℕ} {Z : ℝ} {ψ : SpinSpace N} {q : ℝ}
    (c : ℂ) (hq : coulombH1FormValue N Z ψ q) :
    coulombH1FormValue N Z (c • ψ) (‖c‖^2 * q) := by
  obtain ⟨hψ,d,v,hd,hv,rfl⟩ := hq
  refine ⟨(fermionicSubspace N).smul_mem c hψ,fun k => c • d k,c • v,
    fun σ k => weakPartial_smul c (hd σ k),spin_coulomb_product_smul c hv,?_⟩
  exact (coulombH1Energy_smul c ψ d v).symm

theorem coulombH1FormValue_add_sub_exists {N : ℕ} {Z : ℝ}
    {ψ φ : SpinSpace N} {qψ qφ : ℝ}
    (hψ : coulombH1FormValue N Z ψ qψ) (hφ : coulombH1FormValue N Z φ qφ) :
    ∃ qplus qminus : ℝ,
      coulombH1FormValue N Z (ψ + φ) qplus ∧
      coulombH1FormValue N Z (ψ - φ) qminus ∧
      qplus + qminus = 2 * qψ + 2 * qφ := by
  obtain ⟨hψ,d,v,hd,hv,rfl⟩ := hψ
  obtain ⟨hφ,e,w,he,hw,rfl⟩ := hφ
  refine ⟨coulombH1Energy (ψ + φ) (fun k => d k + e k) (v + w),
    coulombH1Energy (ψ - φ) (fun k => d k - e k) (v - w),?_,?_,
    coulombH1Energy_parallelogram ψ φ d e v w⟩
  · exact ⟨(fermionicSubspace N).add_mem hψ hφ,fun k => d k + e k,v + w,
      fun σ k => weakPartial_add (hd σ k) (he σ k),spin_coulomb_product_add hv hw,rfl⟩
  · exact ⟨(fermionicSubspace N).sub_mem hψ hφ,fun k => d k - e k,v - w,
      fun σ k => weakPartial_sub_h1 (hd σ k) (he σ k),spin_coulomb_product_sub hv hw,rfl⟩

theorem coulombH1FormValue_parallelogram {N : ℕ} {Z : ℝ}
    {ψ φ : SpinSpace N} {qψ qφ qplus qminus : ℝ}
    (hψ : coulombH1FormValue N Z ψ qψ) (hφ : coulombH1FormValue N Z φ qφ)
    (hplus : coulombH1FormValue N Z (ψ + φ) qplus)
    (hminus : coulombH1FormValue N Z (ψ - φ) qminus) :
    qplus + qminus = 2 * qψ + 2 * qφ := by
  obtain ⟨qp,qm,hp,hm,heq⟩ := coulombH1FormValue_add_sub_exists hψ hφ
  rw [coulombH1FormValue_unique hplus hp, coulombH1FormValue_unique hminus hm]
  exact heq

#print axioms coulombH1Energy_smul
#print axioms coulombH1Energy_parallelogram
#print axioms coulombH1FormValue_smul
#print axioms coulombH1FormValue_add_sub_exists
#print axioms coulombH1FormValue_parallelogram

end TheoremT.Continuum
