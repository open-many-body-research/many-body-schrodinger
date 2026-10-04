import SpectatorSmoothSourceWords_v1
import SpectatorIterationState_v1

/-! Region L2 budgets for the actual smooth spectator forcing words.
A finite-measure region and a displayed coefficient-word bound imply the
explicit squared budget C^2 * norm(z)^2 * volume(region). No bound or
regularity of an unknown solution is assumed. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem smooth_spectator_source_region_budget
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) {b : Space κ → ℝ}
    (hb : ContDiffOn ℝ ∞ b Ω) (z : ℂ) (w : List κ)
    {S : Set (Space κ)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (hfinite : volume S < ⊤) {C : ℝ} (_hC : 0 ≤ C)
    (hbound : ∀ p ∈ S, |spectatorWordDeriv b w p| ≤ C) :
    RegionL2Budget (fun p => spectatorWordDeriv b w p • z) S
      (C^2*‖z‖^2*(volume S).toReal) := by
  have hsmooth := spectatorWordDeriv_contDiffOn hΩ hb w
  have hcont : ContinuousOn (fun p => spectatorWordDeriv b w p • z) S :=
    (hsmooth.continuousOn.mono hSΩ).smul continuousOn_const
  have hnorm (p : Space κ) (hp : p ∈ S) :
      ‖spectatorWordDeriv b w p • z‖ ≤ C*‖z‖ := by
    rw [norm_smul,Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hbound p hp) (norm_nonneg z)
  haveI : IsFiniteMeasure (volume.restrict S) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hfinite⟩
  have htop : MemLp (fun p => spectatorWordDeriv b w p • z) ⊤ (volume.restrict S) := by
    apply memLp_top_of_bound (hcont.aestronglyMeasurable hS) (C*‖z‖)
    filter_upwards [ae_restrict_mem hS] with p hp
    exact hnorm p hp
  have hm : MemLp (fun p => spectatorWordDeriv b w p • z) 2 (volume.restrict S) :=
    htop.mono_exponent (by simp)
  refine ⟨hm,?_⟩
  calc
    _ ≤ ∫ _p in S, (C*‖z‖)^2 := by
      apply integral_mono_ae (hm.integrable_norm_pow (by norm_num)) (integrable_const _)
      filter_upwards [ae_restrict_mem hS] with p hp
      exact pow_le_pow_left₀ (norm_nonneg _) (hnorm p hp) 2
    _ = (C*‖z‖)^2*(volume S).toReal := by simp [Measure.real,mul_comm]
    _ = _ := by ring

#print axioms smooth_spectator_source_region_budget
end TheoremT.Continuum.WeakGrushin
