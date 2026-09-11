import GrushinPartialMollifierSupport_v1

noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]

theorem spectator_translated_support_subset_thickening
    {C : Set (KSSpace × T)} {φ : KSSpace × T → ℝ} (hφ : tsupport φ ⊆ C)
    {ε : ℝ} (s : T) (hs : ‖s‖ < ε) :
    tsupport (fun q => φ (q+(0,s))) ⊆ thickening ε C := by
  intro q hq
  have hq' : q+(0,s) ∈ tsupport φ := by
    have he := tsupport_comp_eq_preimage φ (Homeomorph.addRight (0,s))
    change q ∈ tsupport (φ ∘ (Homeomorph.addRight (0,s))) at hq
    rw [he] at hq
    exact hq
  apply mem_thickening_iff.mpr
  refine ⟨q+(0,s),hφ hq',?_⟩
  simpa [dist_eq_norm] using hs

theorem partial_mollifier_shifted_support_uniform_eventually
    {Ω C : Set (KSSpace × T)} (hΩ : IsOpen Ω) (hC : IsCompact C) (hCΩ : C ⊆ Ω) :
    ∀ᶠ n : ℕ in atTop, ∀ φ : KSSpace × T → ℝ, tsupport φ ⊆ C →
      ∀ s : T, GenericMollifier.mollifierKernel n s ≠ 0 →
        tsupport (fun q => φ (q+(0,s))) ⊆ Ω := by
  obtain ⟨ε,hε,hεΩ⟩ := hC.exists_thickening_subset_open hΩ hCΩ
  have hn : ∀ᶠ n : ℕ in atTop, (GenericMollifier.mollifierBump (E := T) n).rOut < ε :=
    (GenericMollifier.mollifierBump_radius_tendsto (E := T)).eventually (gt_mem_nhds hε)
  filter_upwards [hn] with n hn φ hφ s hKs
  have hsrad : ‖s‖ < (GenericMollifier.mollifierBump (E := T) n).rOut := by
    have hh : s ∈ Function.support ((GenericMollifier.mollifierBump (E := T) n).normed volume) := hKs
    rw [ContDiffBump.support_normed_eq] at hh
    simpa only [mem_ball,dist_zero_right] using hh
  exact (spectator_translated_support_subset_thickening hφ s (hsrad.trans hn)).trans hεΩ

#print axioms spectator_translated_support_subset_thickening
#print axioms partial_mollifier_shifted_support_uniform_eventually
end TheoremT.Continuum
