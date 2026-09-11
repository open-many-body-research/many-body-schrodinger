import GenericWeakEllipticGain_v1
import Mathlib.MeasureTheory.Function.LocallyIntegrable

noncomputable section
open MeasureTheory Filter TemperedDistribution
open scoped SchwartzMap Laplacian LineDeriv ContDiff BigOperators
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem generic_test_integrable (f : Lp ℂ 2 (volume : Measure E))
    {φ : E → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Integrable (fun x => φ x • f x) :=
  ((Lp.memLp f).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hφ hc

theorem generic_integral_complex_test_split (f : Lp ℂ 2 (volume : Measure E))
    {φ : E → ℂ} (hφ : Continuous φ) (hcφ : HasCompactSupport φ) :
    (∫ x, φ x • f x) = (∫ x, (φ x).re • f x) + Complex.I • (∫ x, (φ x).im • f x) := by
  have hr := generic_test_integrable f (Complex.continuous_re.comp hφ) (hcφ.comp_left rfl)
  have hi := generic_test_integrable f (Complex.continuous_im.comp hφ) (hcφ.comp_left rfl)
  calc
    (∫ x, φ x • f x) = ∫ x, (φ x).re • f x + Complex.I • ((φ x).im • f x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      calc
        φ x • f x = ((φ x).re + (φ x).im * Complex.I : ℂ) • f x := by rw [Complex.re_add_im]
        _ = _ := by
          simp only [add_smul, mul_smul, Complex.coe_smul]
          rw [smul_comm ((φ x).im) Complex.I]
    _ = _ := by
      have hs := integral_add hr (Integrable.smul Complex.I hi)
      simp only [Pi.smul_apply, Function.comp_apply] at hs
      rw [hs, integral_smul]

theorem generic_compact_laplacian_directional_sum
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {φ : E → F} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℝ E) (x : E) :
    Δ φ x = ∑ k, fderiv ℝ (fun y => fderiv ℝ φ y (b k)) x (b k) := by
  let φS : 𝓢(E,F) := hc.toSchwartzMap hφ
  change Δ (φS : E → F) x = _
  rw [← SchwartzMap.laplacian_apply φS, SchwartzMap.laplacian_eq_sum b]
  simp only [SchwartzMap.sum_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv]
  rfl

theorem generic_compact_laplacian_continuous_compact
    {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    Continuous (Δ φ) ∧ HasCompactSupport (Δ φ) := by
  have he : Δ φ = fun x => ∑ k, fderiv ℝ
      (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E k)) x (stdOrthonormalBasis ℝ E k) :=
    funext (generic_compact_laplacian_directional_sum hφ hc (stdOrthonormalBasis ℝ E))
  rw [he]
  have hd (v : E) : ContDiff ℝ ∞ (fun y => fderiv ℝ φ y v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  constructor
  · exact continuous_finset_sum _ (fun k _ => ((hd _).continuous_fderiv (by simp)).clm_apply continuous_const)
  · have he2 : (fun x => ∑ k, fderiv ℝ
        (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E k)) x (stdOrthonormalBasis ℝ E k)) =
        ∑ k, (fun x => fderiv ℝ (fun y => fderiv ℝ φ y (stdOrthonormalBasis ℝ E k)) x
          (stdOrthonormalBasis ℝ E k)) := by
      funext x; simp
    rw [he2]
    exact HasCompactSupport.finset_sum
      (fun k _ => (hc.fderiv_apply ℝ (stdOrthonormalBasis ℝ E k)).fderiv_apply ℝ (stdOrthonormalBasis ℝ E k))

theorem generic_compact_laplacian_complex_test
    (f w : Lp ℂ 2 (volume : Measure E))
    (h : ∀ φ : E → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ x, φ x • w x) = ∫ x, Δ φ x • f x)
    {φ : E → ℂ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, φ x • w x) = ∫ x, Δ φ x • f x := by
  have hr := h (Complex.reCLM ∘ φ) (Complex.reCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hi := h (Complex.imCLM ∘ φ) (Complex.imCLM.contDiff.comp hφ) (hc.comp_left rfl)
  have hre (x : E) : Δ (Complex.reCLM ∘ φ) x = (Δ φ x).re :=
    (hφ.of_le (by norm_num)).contDiffAt.laplacian_CLM_comp_left
  have him (x : E) : Δ (Complex.imCLM ∘ φ) x = (Δ φ x).im :=
    (hφ.of_le (by norm_num)).contDiffAt.laplacian_CLM_comp_left
  obtain ⟨hΔc,hΔs⟩ := generic_compact_laplacian_continuous_compact hφ hc
  rw [generic_integral_complex_test_split w hφ.continuous hc,
    generic_integral_complex_test_split f hΔc hΔs]
  simp only [Function.comp_apply, Complex.reCLM_apply, Complex.imCLM_apply, hre, him] at hr hi
  rw [hr,hi]

#print axioms generic_compact_laplacian_complex_test
end TheoremT.Continuum
