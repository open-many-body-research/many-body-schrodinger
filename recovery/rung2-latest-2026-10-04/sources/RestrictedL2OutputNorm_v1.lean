import GrushinLocalL2Extension_v1
import MeasureBoundedRealMultiplier_v1
import WeakGrushinJetLimits_v1

/-! Triangle bound for an actual globally supported output from its
restricted L2 source representatives. This concerns genuine L2 norms; the
zero extension is only a mathematical representative, never differentiated. -/
noncomputable section
open MeasureTheory Filter
namespace TheoremT.Continuum
variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

theorem restrictedL2Extension_norm (Ω : Set X) (hΩ : MeasurableSet Ω)
    (f : Lp ℂ 2 (μ.restrict Ω)) :
    ‖restrictedL2Extension Ω hΩ f (Lp.memLp f)‖ = ‖f‖ := by
  have he := restrictedL2Extension_norm_sq Ω hΩ f (Lp.memLp f)
  rw [← WeakGrushin.l2_norm_sq_integral] at he
  nlinarith [norm_nonneg (restrictedL2Extension Ω hΩ f (Lp.memLp f)),norm_nonneg f]

theorem supported_output_norm_le_restricted (Ω : Set X) (hΩ : MeasurableSet Ω)
    (H : Lp ℂ 2 μ) (J : Lp ℂ 2 (μ.restrict Ω))
    (hHJ : H =ᵐ[μ.restrict Ω] J) (hoff : ∀ᵐ p ∂μ, p ∉ Ω → H p = 0) :
    ‖H‖ = ‖J‖ := by
  have heq : H = restrictedL2Extension Ω hΩ J (Lp.memLp J) := by
    apply Lp.ext
    filter_upwards [(ae_restrict_iff' hΩ).mp hHJ,hoff,
      restrictedL2Extension_ae Ω hΩ J (Lp.memLp J)] with p hp hq hr
    rw [hr]
    by_cases hm : p ∈ Ω
    · simpa only [Set.indicator_of_mem hm] using hp hm
    · simpa only [Set.indicator_of_notMem hm] using hq hm
  rw [heq,restrictedL2Extension_norm]

theorem restricted_cutoff_output_norm (Ω : Set X) (hΩ : MeasurableSet Ω)
    (χ B : X → ℝ) (f h err : X → ℂ)
    (hχm : MemLp χ ⊤ (μ.restrict Ω)) (hBm : MemLp B ⊤ (μ.restrict Ω))
    (hχb : ∀ᵐ p ∂μ.restrict Ω, ‖χ p‖ ≤ 1) {M : ℝ}
    (hBb : ∀ᵐ p ∂μ.restrict Ω, ‖B p‖ ≤ M)
    (HF HS HE : Lp ℂ 2 (μ.restrict Ω))
    (hF : HF =ᵐ[μ.restrict Ω] f) (hS : HS =ᵐ[μ.restrict Ω] h)
    (hE : HE =ᵐ[μ.restrict Ω] err)
    (H : Lp ℂ 2 μ)
    (hH : H =ᵐ[μ] (fun p => χ p • (h p-B p • f p)-err p))
    (hoffχ : ∀ p, p ∉ Ω → χ p = 0) (hoffE : ∀ p, p ∉ Ω → err p = 0) :
    ‖H‖ ≤ ‖HS‖+M*‖HF‖+‖HE‖ := by
  let HB := measureBoundedRealMul B hBm HF
  let HC := measureBoundedRealMul χ hχm (HS-HB)
  let J := HC-HE
  have hJ : J =ᵐ[μ.restrict Ω] (fun p => χ p • (h p-B p • f p)-err p) := by
    filter_upwards [Lp.coeFn_sub HC HE,measureBoundedRealMul_ae χ hχm (HS-HB),
      Lp.coeFn_sub HS HB,measureBoundedRealMul_ae B hBm HF,hF,hS,hE] with p hj hc hs hb hf hh he
    change J p = _
    change (HC-HE) p = _
    rw [hj]
    change HC p-HE p = _
    rw [hc,hs]
    change χ p • (HS p-HB p)-HE p = _
    rw [hb,hf,hh,he]
  have hHr : H =ᵐ[μ.restrict Ω] (fun p => χ p • (h p-B p • f p)-err p) := ae_restrict_of_ae hH
  have hHJ : H =ᵐ[μ.restrict Ω] J := hHr.trans hJ.symm
  have hoff : ∀ᵐ p ∂μ, p ∉ Ω → H p = 0 := by
    filter_upwards [hH] with p hp hm
    rw [hp,hoffχ p hm,hoffE p hm,zero_smul,sub_zero]
  rw [supported_output_norm_le_restricted Ω hΩ H J hHJ hoff]
  have hcn : ‖HC‖ ≤ ‖HS-HB‖ := by
    simpa only [one_mul] using measureBoundedRealMul_norm_le χ hχm hχb (HS-HB)
  have hbn : ‖HB‖ ≤ M*‖HF‖ := measureBoundedRealMul_norm_le B hBm hBb HF
  calc
    ‖J‖ ≤ ‖HC‖+‖HE‖ := norm_sub_le HC HE
    _ ≤ (‖HS‖+‖HB‖)+‖HE‖ := add_le_add (hcn.trans (norm_sub_le HS HB)) le_rfl
    _ ≤ _ := add_le_add (add_le_add le_rfl hbn) le_rfl

end TheoremT.Continuum
