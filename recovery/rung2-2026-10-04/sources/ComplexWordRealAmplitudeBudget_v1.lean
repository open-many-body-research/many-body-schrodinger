import ComplexWordRealAmplitude_v1
import SpectatorSmoothSourceRegionBudget_v1
import ProductWeakFiniteFamilyUnique_v1

/-! A pointwise real coefficient-word bound on a measurable finite region
gives an actual L2 budget for the corresponding complex full source word.
The complex derivative is identified before almost-everywhere transfer of
the constructed budget. No source budget or unknown-solution bound is assumed. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped ContDiff

namespace TheoremT.Continuum.WeakGrushin

variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem complex_word_real_amplitude_region_budget {ι : Type}
    (dirs : ι → Space κ) {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {b : Space κ → ℝ} (hb : ContDiffOn ℝ ∞ b Ω) (z : ℂ) (w : List ι)
    {S : Set (Space κ)} (hS : MeasurableSet S) (hSΩ : S ⊆ Ω)
    (hfinite : volume S < ⊤) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ p ∈ S, |directionalWordDeriv dirs b w p| ≤ C) :
    RegionL2Budget (complexDirectionalWordDeriv dirs (fun p => b p • z) w) S
      (C^2*‖z‖^2*(volume S).toReal) := by
  have hraw : RegionL2Budget (fun p => directionalWordDeriv dirs b w p • z) S
      (C^2*‖z‖^2*(volume S).toReal) :=
    smooth_spectator_source_region_budget hΩ
      (directionalWordDeriv_contDiffOn dirs hΩ hb w) z [] hS hSΩ hfinite hC hbound
  apply hraw.congr_ae
  filter_upwards [ae_restrict_mem hS] with p hp
  exact (complexDirectionalWordDeriv_real_smul_const dirs hΩ hb z w (hSΩ hp)).symm

end TheoremT.Continuum.WeakGrushin
