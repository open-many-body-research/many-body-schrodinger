import CompactWeakGrushinCutoffEnergy_v1
import CompactWeakGrushinOutputEstimates_v1
import ActualL2IntegralCauchy_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem cutoff_l2_pairing_le_half
    {η : Space κ → ℝ} (hη : Continuous η) (hcη : HasCompactSupport η)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    {w : Space κ → ℂ} (hw : MemLp w 2 volume) :
    (∫ p, inner ℝ ((η p)^2 • f p) (w p)) ≤
      ((∫ p, (η p)^2*‖f p‖^2)+(∫ p, (η p)^2*‖w p‖^2))/2 := by
  have hm : MemLp η ⊤ volume := hη.memLp_top_of_hasCompactSupport hcη volume
  have hf : MemLp (fun p => η p • f p) 2 volume := by
    simpa only [Pi.smul_def'] using (Lp.memLp f).smul hm
  have hW : MemLp (fun p => η p • w p) 2 volume := by
    simpa only [Pi.smul_def'] using hw.smul hm
  have he : (∫ p, inner ℝ ((η p)^2 • f p) (w p)) =
      ∫ p, inner ℝ (η p • f p) (η p • w p) := by
    apply integral_congr_ae
    filter_upwards [] with p
    simp only [real_inner_smul_left,real_inner_smul_right]
    ring
  calc
    _ = ∫ p, inner ℝ (η p • f p) (η p • w p) := he
    _ ≤ ‖hf.toLp (fun p => η p • f p)‖ * ‖hW.toLp (fun p => η p • w p)‖ :=
      (le_abs_self _).trans (actual_l2_integral_inner_abs_le hf hW)
    _ ≤ (‖hf.toLp (fun p => η p • f p)‖^2 + ‖hW.toLp (fun p => η p • w p)‖^2)/2 := by
      nlinarith [sq_nonneg (‖hf.toLp (fun p => η p • f p)‖ - ‖hW.toLp (fun p => η p • w p)‖)]
    _ = _ := by
      rw [actual_l2_toLp_norm_sq_integral hf,actual_l2_toLp_norm_sq_integral hW]
      simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs]

theorem compact_weakH2_cutoff_caccioppoli {c : ℝ} (hc0 : 0 ≤ c)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    cutoffGradient c η f d ≤
      ((∫ p, (η p)^2*‖f p‖^2)+(∫ p, (η p)^2*‖principal c e p‖^2))/2 +
        grushinCutoffEnergy c η f := by
  have hP := (compact_weakH2_estimates hc0 d e hd he hK hs).1
  rw [compact_weakH2_cutoff_energy c hη hcη d e hd he hK hs]
  exact add_le_add (cutoff_l2_pairing_le_half hη.continuous hcη f hP) (le_refl _)

theorem compact_weakH2_cutoff_caccioppoli_output {c : ℝ} (hc0 : 0 ≤ c)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    cutoffGradient c η f d ≤
      ((∫ p, (η p)^2*‖f p‖^2)+(∫ p, (η p)^2*‖h p‖^2))/2 +
        grushinCutoffEnergy c η f := by
  have ha := principal_ae_eq_of_weak_output c d e hd he hP
  have hb := compact_weakH2_cutoff_caccioppoli hc0 hη hcη d e hd he hK hs
  have heq : (∫ p, (η p)^2*‖principal c e p‖^2) = ∫ p, (η p)^2*‖h p‖^2 := by
    apply integral_congr_ae
    filter_upwards [ha] with p hp
    rw [hp]
  simpa only [heq] using hb

end TheoremT.Continuum.WeakGrushin
