import GenericCompactLaplacianProduct_v1
import GenericBoundedSmoothMultiplier_v1

/-! Localizing an actual compact-test Laplacian equation in divergence form.
Only L² functions are given; this formula neither assumes nor uses a first
weak derivative of the input. -/
noncomputable section
open MeasureTheory Filter
open scoped Laplacian ContDiff
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_cutoff_laplacian_integral
    {Ω : Set E} (f w : Lp ℂ 2 (volume : Measure E))
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Δ φ x • f x) = ∫ x, φ x • w x)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hcφ : HasCompactSupport φ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    (∫ x, (χ x * Δ φ x) • f x) =
      (∫ x, (χ x * φ x) • w x) - (∫ x, (Δ χ x * φ x) • f x) -
        ∑ i, ∫ x, (2 * fderiv ℝ χ x (b i) * fderiv ℝ φ x (b i)) • f x := by
  have hdχ := (generic_real_compact_laplacian_continuous_compact hχ hcχ).1
  have hdφ := (generic_real_compact_laplacian_continuous_compact hφ hcφ).1
  have ia : Integrable (fun x => (Δ χ x * φ x) • f x) :=
    generic_real_test_integrable f (hdχ.mul hφ.continuous) hcφ.mul_left
  have ic : Integrable (fun x => (χ x * Δ φ x) • f x) :=
    generic_real_test_integrable f (hχ.continuous.mul hdφ) hcχ.mul_right
  have ib (i : ι) : Integrable
      (fun x => (2 * fderiv ℝ χ x (b i) * fderiv ℝ φ x (b i)) • f x) := by
    apply generic_real_test_integrable f
    · exact (continuous_const.mul ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)).mul
        ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
    · exact (hcφ.fderiv_apply ℝ (b i)).mul_left
  have is : Integrable (fun x => ∑ i, (2 * fderiv ℝ χ x (b i) *
      fderiv ℝ φ x (b i)) • f x) := integrable_finset_sum _ (fun i _ => ib i)
  have hp := h (fun x => χ x * φ x) (hχ.mul hφ) hcχ.mul_right
    ((tsupport_mul_subset_left).trans hsχ)
  have he : (∫ x, Δ (fun y => χ y * φ y) x • f x) =
      ((∫ x, (Δ χ x * φ x) • f x) +
        ∑ i, ∫ x, (2 * fderiv ℝ χ x (b i) * fderiv ℝ φ x (b i)) • f x) +
          (∫ x, (χ x * Δ φ x) • f x) := by
    have hh (x : E) : Δ (fun y => χ y * φ y) x • f x =
        ((Δ χ x * φ x) • f x +
          ∑ i, (2 * fderiv ℝ χ x (b i) * fderiv ℝ φ x (b i)) • f x) +
          (χ x * Δ φ x) • f x := by
      rw [generic_compact_laplacian_mul hχ hcχ hφ hcφ b x]
      simp only [add_smul, Finset.mul_sum, Finset.sum_smul, mul_assoc]
    simp_rw [hh]
    have ias : Integrable (fun x => (Δ χ x * φ x) • f x +
      ∑ i, (2 * fderiv ℝ χ x (b i) * fderiv ℝ φ x (b i)) • f x) := ia.add is
    rw [integral_add ias ic, integral_add ia is, integral_finset_sum _ (fun i _ => ib i)]
  rw [he] at hp
  rw [← hp]
  abel

theorem generic_cutoff_laplacian_divergence_test_witnesses
    {Ω : Set E} (f w : Lp ℂ 2 (volume : Measure E))
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ x, Δ φ x • f x) = ∫ x, φ x • w x)
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (hsχ : tsupport χ ⊆ Ω)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) :
    ∃ U A : Lp ℂ 2 (volume : Measure E), ∃ B : ι → Lp ℂ 2 (volume : Measure E),
      U =ᵐ[volume] (fun x => χ x • f x) ∧
      A =ᵐ[volume] (fun x => χ x • w x - Δ χ x • f x) ∧
      (∀ i, B i =ᵐ[volume] (fun x => (2 * fderiv ℝ χ x (b i)) • f x)) ∧
      ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x, Δ φ x • U x) =
          (∫ x, φ x • A x) - ∑ i, ∫ x, fderiv ℝ φ x (b i) • B i x := by
  have hχm := hχ.continuous.memLp_top_of_hasCompactSupport hcχ volume
  obtain ⟨hdχ, hcdχ⟩ := generic_real_compact_laplacian_continuous_compact hχ hcχ
  have hΔm := hdχ.memLp_top_of_hasCompactSupport hcdχ volume
  have hDm (i : ι) : MemLp (fun x => 2 * fderiv ℝ χ x (b i)) ⊤ volume :=
    (continuous_const.mul ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)).memLp_top_of_hasCompactSupport
      (hcχ.fderiv_apply ℝ (b i)).mul_left volume
  let U := genericBoundedRealMul χ hχm f
  let A := genericBoundedRealMul χ hχm w - genericBoundedRealMul (Δ χ) hΔm f
  let B (i : ι) := genericBoundedRealMul (fun x => 2 * fderiv ℝ χ x (b i)) (hDm i) f
  have hU : U =ᵐ[volume] (fun x => χ x • f x) := genericBoundedRealMul_ae _ _ _
  have hA : A =ᵐ[volume] (fun x => χ x • w x - Δ χ x • f x) := by
    filter_upwards [Lp.coeFn_sub (genericBoundedRealMul χ hχm w)
      (genericBoundedRealMul (Δ χ) hΔm f), genericBoundedRealMul_ae χ hχm w,
      genericBoundedRealMul_ae (Δ χ) hΔm f] with x hx hw hf
    change (genericBoundedRealMul χ hχm w - genericBoundedRealMul (Δ χ) hΔm f) x = _
    rw [hx]
    change genericBoundedRealMul χ hχm w x - genericBoundedRealMul (Δ χ) hΔm f x = _
    rw [hw,hf]
  have hB (i : ι) : B i =ᵐ[volume] (fun x => (2 * fderiv ℝ χ x (b i)) • f x) :=
    genericBoundedRealMul_ae _ _ _
  refine ⟨U,A,B,hU,hA,hB,?_⟩
  intro φ hφ hcφ
  have hu : (∫ x, Δ φ x • U x) = ∫ x, (χ x * Δ φ x) • f x := by
    apply integral_congr_ae
    filter_upwards [hU] with x hx
    rw [hx, ← mul_smul, mul_comm]
  have ha : (∫ x, φ x • A x) =
      (∫ x, (χ x * φ x) • w x) - ∫ x, (Δ χ x * φ x) • f x := by
    calc
      _ = ∫ x, (χ x * φ x) • w x - (Δ χ x * φ x) • f x := by
        apply integral_congr_ae
        filter_upwards [hA] with x hx
        rw [hx,smul_sub,← mul_smul,← mul_smul,mul_comm (φ x) (χ x),mul_comm (φ x) (Δ χ x)]
      _ = _ := integral_sub
        (generic_real_test_integrable w (hχ.continuous.mul hφ.continuous) hcφ.mul_left)
        (generic_real_test_integrable f (hdχ.mul hφ.continuous) hcφ.mul_left)
  have hb (i : ι) : (∫ x, fderiv ℝ φ x (b i) • B i x) =
      ∫ x, (2 * fderiv ℝ χ x (b i) * fderiv ℝ φ x (b i)) • f x := by
    apply integral_congr_ae
    filter_upwards [hB i] with x hx
    rw [hx,← mul_smul,mul_comm]
  rw [hu,ha]
  simp_rw [hb]
  exact generic_cutoff_laplacian_integral f w h hχ hcχ hsχ hφ hcφ b

#print axioms generic_cutoff_laplacian_integral
#print axioms generic_cutoff_laplacian_divergence_test_witnesses
end TheoremT.Continuum
