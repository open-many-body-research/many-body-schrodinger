import BoundedSmoothMultiplier_v1
import HardyWeakLaplacian_v1
import CutoffConvergence_v2

/-! Exact L² algebra and real inner-product symmetry for bounded real weights. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem boundedRealMul_add {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : MemLp χ ⊤ volume) (f g : SpatialL2 N) :
    boundedRealMul χ hχ (f+g) = boundedRealMul χ hχ f + boundedRealMul χ hχ g := by
  apply Lp.ext
  filter_upwards [boundedRealMul_ae χ hχ (f+g),boundedRealMul_ae χ hχ f,
    boundedRealMul_ae χ hχ g,Lp.coeFn_add f g,
    Lp.coeFn_add (boundedRealMul χ hχ f) (boundedRealMul χ hχ g)] with x hx hf hg hs ht
  simp only [Pi.add_apply] at *
  rw [hx,hs,ht,hf,hg,smul_add]

theorem boundedRealMul_smul {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : MemLp χ ⊤ volume) (c : ℂ) (f : SpatialL2 N) :
    boundedRealMul χ hχ (c • f) = c • boundedRealMul χ hχ f := by
  apply Lp.ext
  filter_upwards [boundedRealMul_ae χ hχ (c • f),boundedRealMul_ae χ hχ f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (boundedRealMul χ hχ f)] with x hx hf hs ht
  simp only [Pi.smul_apply] at *
  rw [hx,hs,ht,hf,smul_comm]

theorem boundedRealMul_real_inner {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : MemLp χ ⊤ volume) (f g : SpatialL2 N) :
    inner ℝ (boundedRealMul χ hχ f) g = inner ℝ f (boundedRealMul χ hχ g) := by
  rw [L2.inner_def,L2.inner_def]
  apply integral_congr_ae
  filter_upwards [boundedRealMul_ae χ hχ f,boundedRealMul_ae χ hχ g] with x hf hg
  rw [hf,hg,inner_smul_left,inner_smul_right]
  simp

theorem boundedRealMul_comm {N : ℕ} (χ η : Configuration N → ℝ)
    (hχ : MemLp χ ⊤ volume) (hη : MemLp η ⊤ volume) (f : SpatialL2 N) :
    boundedRealMul χ hχ (boundedRealMul η hη f) =
      boundedRealMul η hη (boundedRealMul χ hχ f) := by
  apply Lp.ext
  filter_upwards [boundedRealMul_ae χ hχ (boundedRealMul η hη f),
    boundedRealMul_ae η hη (boundedRealMul χ hχ f),boundedRealMul_ae χ hχ f,
    boundedRealMul_ae η hη f] with x hx hy hf hg
  rw [hx,hy,hf,hg,smul_comm]

theorem boundedRealMul_norm_sq_integral {N : ℕ} (χ : Configuration N → ℝ)
    (hχ : MemLp χ ⊤ volume) (f : SpatialL2 N) :
    ‖boundedRealMul χ hχ f‖^2 = ∫ x, (χ x)^2 * ‖f x‖^2 := by
  rw [spatialL2_norm_sq_integral]
  apply integral_congr_ae
  filter_upwards [boundedRealMul_ae χ hχ f] with x hx
  rw [hx,norm_smul,mul_pow,Real.norm_eq_abs,sq_abs]

theorem boundedRealMul_coulomb_ae {N : ℕ} {Z : ℝ} (χ : Configuration N → ℝ)
    (hχ : MemLp χ ⊤ volume) {f v : SpatialL2 N}
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    boundedRealMul χ hχ v =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ) * boundedRealMul χ hχ f x := by
  filter_upwards [hv,boundedRealMul_ae χ hχ v,boundedRealMul_ae χ hχ f] with x hvx hx hf
  rw [hx,hf,hvx]
  simp only [Complex.real_smul]
  ring

#print axioms boundedRealMul_real_inner
#print axioms boundedRealMul_coulomb_ae
end TheoremT.Continuum
