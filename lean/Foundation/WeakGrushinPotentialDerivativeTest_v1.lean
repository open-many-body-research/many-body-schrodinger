import ProductWeakEllipticGain_v1
import SmoothLocalTestProduct_v1

/-! Local potential Leibniz identity against actual compact joint tests.
Only smoothness on the open coefficient domain is assumed. The products
with tests are proved smooth and compact before invoking weak derivatives
and Bochner integral algebra. Global L2 membership of B f is not assumed.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem local_potential_test_fderiv_product
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {Ω : Set E} (hΩ : IsOpen Ω) {B : E → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {φ : E → ℝ} (hφ : ContDiff ℝ ∞ φ) (hs : tsupport φ ⊆ Ω)
    (v x : E) :
    fderiv ℝ (fun y => φ y * B y) x v =
      φ x * fderiv ℝ B x v + fderiv ℝ φ x v * B x := by
  by_cases hx : x ∈ tsupport φ
  · have hh := (hφ.differentiable (by simp) x).hasFDerivAt.mul
      ((hB.contDiffAt (hΩ.mem_nhds (hs hx))).differentiableAt (by simp)).hasFDerivAt
    change HasFDerivAt (𝕜 := ℝ) (fun y => φ y * B y) _ x at hh
    rw [hh.fderiv]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,smul_eq_mul]
    ring
  · have hp : x ∉ tsupport (fun y => φ y * B y) :=
      fun hh => hx (tsupport_mul_subset_left hh)
    simp only [fderiv_of_notMem_tsupport ℝ hp,fderiv_of_notMem_tsupport ℝ hx,
      ContinuousLinearMap.zero_apply,image_eq_zero_of_notMem_tsupport hx,zero_mul,add_zero]

variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProduct_directional_local_potential_test
    {f d : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (hd : WeakProductL2Directional f d v)
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω)
    {B : Y × T → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {φ : Y × T → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hs : tsupport φ ⊆ Ω) :
    Integrable (fun p => φ p • (B p • d p + fderiv ℝ B p v • f p)) volume ∧
    Integrable (fun p => fderiv ℝ φ p v • (B p • f p)) volume ∧
    (∫ p, φ p • (B p • d p + fderiv ℝ B p v • f p)) =
      -(∫ p, fderiv ℝ φ p v • (B p • f p)) := by
  have hBon (p : Y × T) (hp : p ∈ Ω) : ContDiffAt ℝ ∞ B p :=
    hB.contDiffAt (hΩ.mem_nhds hp)
  have hφB : ContDiff ℝ ∞ (fun p => φ p * B p) :=
    smooth_mul_of_smooth_on_tsupport hφ (fun p hp => hBon p (hs hp))
  have hφDB : ContDiff ℝ ∞ (fun p => φ p * fderiv ℝ B p v) :=
    smooth_mul_of_smooth_on_tsupport hφ
      (fun p hp => local_contDiffAt_directional_derivative (hBon p (hs hp)) v)
  have hDφ : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v) :=
    (hφ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hDφB : ContDiff ℝ ∞ (fun p => fderiv ℝ φ p v * B p) :=
    smooth_mul_of_smooth_on_tsupport hDφ
      (fun p hp => hBon p (hs (tsupport_fderiv_apply_subset ℝ v hp)))
  have hint (g : Lp ℂ 2 (volume : Measure (Y × T)))
      {ψ : Y × T → ℝ} (hψ : Continuous ψ) (hcψ : HasCompactSupport ψ) :
      Integrable (fun p => ψ p • g p) volume :=
    ((Lp.memLp g).locallyIntegrable (by norm_num)).integrable_smul_left_of_hasCompactSupport hψ hcψ
  have h1 : Integrable (fun p => (φ p * B p) • d p) volume :=
    hint d hφB.continuous hc.mul_right
  have h2 : Integrable (fun p => (φ p * fderiv ℝ B p v) • f p) volume :=
    hint f hφDB.continuous hc.mul_right
  have h3 : Integrable (fun p => (fderiv ℝ φ p v * B p) • f p) volume :=
    hint f hDφB.continuous (hc.fderiv_apply ℝ v).mul_right
  have hw := hd (fun p => φ p * B p) hφB hc.mul_right
  have he : (∫ p, fderiv ℝ (fun q => φ q * B q) p v • f p) =
      (∫ p, (φ p * fderiv ℝ B p v) • f p) +
      (∫ p, (fderiv ℝ φ p v * B p) • f p) := by
    simp_rw [local_potential_test_fderiv_product hΩ hB hφ hs,add_smul]
    exact integral_add h2 h3
  rw [he] at hw
  refine ⟨?_,?_,?_⟩
  · simp only [smul_add,← mul_smul]
    exact h1.fun_add h2
  · simpa only [← mul_smul] using h3
  · simp only [smul_add,← mul_smul]
    rw [integral_add h1 h2,hw]
    abel

#print axioms local_potential_test_fderiv_product
#print axioms weakProduct_directional_local_potential_test
end TheoremT.Continuum
