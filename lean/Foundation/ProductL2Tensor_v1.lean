import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic

/-! Actual products of scalar L2 functions on product measures.
No completed tensor-product identification or supplied operator norm is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.ProductL2
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
variable {μ : Measure X} {ν : Measure Y} [SFinite μ] [SFinite ν]

 theorem norm_sq_integral (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), L2.inner_def,
    ← integral_re (L2.integrable_inner f f)]
  simp [inner_self_eq_norm_sq_to_K, ← Complex.ofReal_pow]

theorem tensor_memLp (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    MemLp (fun z : X × Y => f z.1 * g z.2) 2 (μ.prod ν) := by
  have hm : AEStronglyMeasurable (fun z : X × Y => f z.1 * g z.2) (μ.prod ν) :=
    (Lp.aestronglyMeasurable f).comp_fst.mul (Lp.aestronglyMeasurable g).comp_snd
  apply (memLp_two_iff_integrable_sq_norm hm).mpr
  have hf := (Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hg := (Lp.memLp g).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  simpa only [norm_mul, mul_pow] using hf.mul_prod hg

def tensor (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) : Lp ℂ 2 (μ.prod ν) :=
  (tensor_memLp f g).toLp (fun z => f z.1 * g z.2)

theorem tensor_ae (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    tensor f g =ᵐ[μ.prod ν] fun z => f z.1 * g z.2 :=
  (tensor_memLp f g).coeFn_toLp

theorem tensor_norm_sq (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    ‖tensor f g‖^2 = ‖f‖^2 * ‖g‖^2 := by
  rw [norm_sq_integral]
  have he : (∫ z, ‖tensor f g z‖^2 ∂μ.prod ν) =
      ∫ z : X × Y, ‖f z.1‖^2 * ‖g z.2‖^2 ∂μ.prod ν := by
    apply integral_congr_ae
    filter_upwards [tensor_ae f g] with z hz
    rw [hz,norm_mul,mul_pow]
  rw [he,integral_prod_mul (fun x => ‖f x‖^2) (fun y => ‖g y‖^2),
    ← norm_sq_integral,← norm_sq_integral]

theorem tensor_norm (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) :
    ‖tensor f g‖ = ‖f‖ * ‖g‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp
  rw [tensor_norm_sq,mul_pow]

theorem tensor_add_right (f : Lp ℂ 2 μ) (g h : Lp ℂ 2 ν) :
    tensor f (g+h) = tensor f g + tensor f h := by
  apply Lp.ext
  have ha : ∀ᵐ z : X × Y ∂μ.prod ν, (g+h) z.2 = g z.2 + h z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_add g h)
  filter_upwards [tensor_ae f (g+h),tensor_ae f g,tensor_ae f h,
    Lp.coeFn_add (tensor f g) (tensor f h),ha] with z hz hzg hzh hs ha
  simp only [Pi.add_apply] at hs
  rw [hz,hs,hzg,hzh,ha,mul_add]

theorem tensor_smul_right (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (c : ℂ) :
    tensor f (c • g) = c • tensor f g := by
  apply Lp.ext
  have ha : ∀ᵐ z : X × Y ∂μ.prod ν, (c • g) z.2 = c * g z.2 :=
    (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c g)
  filter_upwards [tensor_ae f (c • g),tensor_ae f g,
    Lp.coeFn_smul c (tensor f g),ha] with z hz hzg hs ha
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  rw [hz,hs,hzg,ha]
  ring

theorem tensor_add_left (f g : Lp ℂ 2 μ) (h : Lp ℂ 2 ν) :
    tensor (f+g) h = tensor f h + tensor g h := by
  apply Lp.ext
  have ha : ∀ᵐ z : X × Y ∂μ.prod ν, (f+g) z.1 = f z.1 + g z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_add f g)
  filter_upwards [tensor_ae (f+g) h,tensor_ae f h,tensor_ae g h,
    Lp.coeFn_add (tensor f h) (tensor g h),ha] with z hz hzf hzg hs ha
  simp only [Pi.add_apply] at hs
  rw [hz,hs,hzf,hzg,ha,add_mul]

theorem tensor_smul_left (f : Lp ℂ 2 μ) (g : Lp ℂ 2 ν) (c : ℂ) :
    tensor (c • f) g = c • tensor f g := by
  apply Lp.ext
  have ha : ∀ᵐ z : X × Y ∂μ.prod ν, (c • f) z.1 = c * f z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae (Lp.coeFn_smul c f)
  filter_upwards [tensor_ae (c • f) g,tensor_ae f g,
    Lp.coeFn_smul c (tensor f g),ha] with z hz hzg hs ha
  simp only [Pi.smul_apply,smul_eq_mul] at hs
  rw [hz,hs,hzg,ha]
  ring

theorem tensor_inner (f h : Lp ℂ 2 μ) (g k : Lp ℂ 2 ν) :
    inner ℂ (tensor f g) (tensor h k) = inner ℂ f h * inner ℂ g k := by
  rw [L2.inner_def,L2.inner_def,L2.inner_def]
  have he : (∫ z, inner ℂ (tensor f g z) (tensor h k z) ∂μ.prod ν) =
      ∫ z : X × Y, inner ℂ (f z.1) (h z.1) * inner ℂ (g z.2) (k z.2) ∂μ.prod ν := by
    apply integral_congr_ae
    filter_upwards [tensor_ae f g,tensor_ae h k] with z hz hw
    rw [hz,hw]
    simp only [RCLike.inner_apply,map_mul]
    ring
  rw [he,integral_prod_mul (fun x => inner ℂ (f x) (h x))
    (fun y => inner ℂ (g y) (k y))]

#print axioms tensor_memLp
#print axioms tensor_norm
#print axioms tensor_add_right
#print axioms tensor_smul_right
#print axioms tensor_add_left
#print axioms tensor_smul_left
#print axioms tensor_inner
end TheoremT.ProductL2
