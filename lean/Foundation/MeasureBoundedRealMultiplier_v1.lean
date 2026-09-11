import GenericBoundedSmoothMultiplier_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum
variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

def measureBoundedRealMul (χ : α → ℝ) (hχ : MemLp χ ⊤ μ)
    (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  ((Lp.memLp f).smul hχ).toLp (fun x => χ x • f x)

theorem measureBoundedRealMul_ae (χ : α → ℝ) (hχ : MemLp χ ⊤ μ)
    (f : Lp ℂ 2 μ) : measureBoundedRealMul χ hχ f =ᵐ[μ] (fun x => χ x • f x) :=
  MemLp.coeFn_toLp _

theorem measureBoundedRealMul_add (χ : α → ℝ) (hχ : MemLp χ ⊤ μ)
    (f g : Lp ℂ 2 μ) :
    measureBoundedRealMul χ hχ (f+g) = measureBoundedRealMul χ hχ f + measureBoundedRealMul χ hχ g := by
  apply Lp.ext
  filter_upwards [measureBoundedRealMul_ae χ hχ (f+g),measureBoundedRealMul_ae χ hχ f,
    measureBoundedRealMul_ae χ hχ g,Lp.coeFn_add f g,
    Lp.coeFn_add (measureBoundedRealMul χ hχ f) (measureBoundedRealMul χ hχ g)] with x hx hf hg hs ht
  simp only [Pi.add_apply] at *
  rw [hx,hs,ht,hf,hg,smul_add]

theorem measureBoundedRealMul_smul (χ : α → ℝ) (hχ : MemLp χ ⊤ μ)
    (c : ℂ) (f : Lp ℂ 2 μ) :
    measureBoundedRealMul χ hχ (c • f) = c • measureBoundedRealMul χ hχ f := by
  apply Lp.ext
  filter_upwards [measureBoundedRealMul_ae χ hχ (c • f),measureBoundedRealMul_ae χ hχ f,
    Lp.coeFn_smul c f,Lp.coeFn_smul c (measureBoundedRealMul χ hχ f)] with x hx hf hs ht
  simp only [Pi.smul_apply] at *
  rw [hx,hs,ht,hf,smul_comm]

theorem measureBoundedRealMul_norm_le (χ : α → ℝ) (hχ : MemLp χ ⊤ μ)
    {C : ℝ} (hb : ∀ᵐ x ∂μ, ‖χ x‖ ≤ C) (f : Lp ℂ 2 μ) :
    ‖measureBoundedRealMul χ hχ f‖ ≤ C * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [measureBoundedRealMul_ae χ hχ f,hb] with x hx hc
  rw [hx,norm_smul]
  exact mul_le_mul_of_nonneg_right hc (norm_nonneg _)

def measureBoundedRealMulCLM (χ : α → ℝ) (hχ : MemLp χ ⊤ μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖χ x‖ ≤ C) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  ({ toFun := measureBoundedRealMul χ hχ
     map_add' := measureBoundedRealMul_add χ hχ
     map_smul' := measureBoundedRealMul_smul χ hχ } : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ).mkContinuous C
    (measureBoundedRealMul_norm_le χ hχ hb)

theorem measureBoundedRealMul_tendsto (χ : α → ℝ) (hχ : MemLp χ ⊤ μ)
    (C : ℝ) (hb : ∀ᵐ x ∂μ, ‖χ x‖ ≤ C)
    {g : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ} (hg : Tendsto g atTop (𝓝 f)) :
    Tendsto (fun n => measureBoundedRealMul χ hχ (g n)) atTop
      (𝓝 (measureBoundedRealMul χ hχ f)) :=
  ((measureBoundedRealMulCLM χ hχ C hb).continuous.tendsto f).comp hg

#print axioms measureBoundedRealMulCLM
#print axioms measureBoundedRealMul_tendsto
end TheoremT.Continuum
