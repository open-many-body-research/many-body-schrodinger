import PartialMollifierConvergence_v1
import GrushinPartialConvolutionWeak_v1
import Mathlib.Topology.MetricSpace.Thickening

noncomputable section
open MeasureTheory Filter Metric
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]

theorem partial_mollifier_shifted_support_eventually
    {Ω : Set (KSSpace × T)} (hΩ : IsOpen Ω) {φ : KSSpace × T → ℝ}
    (hc : HasCompactSupport φ) (hs : tsupport φ ⊆ Ω) :
    ∀ᶠ n : ℕ in atTop, ∀ s : T, GenericMollifier.mollifierKernel n s ≠ 0 →
      tsupport (fun q => φ (q+(0,s))) ⊆ Ω := by
  obtain ⟨ε,hε,hεΩ⟩ := hc.isCompact.exists_thickening_subset_open hΩ hs
  have hn : ∀ᶠ n : ℕ in atTop, (GenericMollifier.mollifierBump (E := T) n).rOut < ε :=
    (GenericMollifier.mollifierBump_radius_tendsto (E := T)).eventually (gt_mem_nhds hε)
  filter_upwards [hn] with n hn s hKs q hq
  have hsrad : ‖s‖ < (GenericMollifier.mollifierBump (E := T) n).rOut := by
    have hh : s ∈ Function.support ((GenericMollifier.mollifierBump (E := T) n).normed volume) := hKs
    rw [ContDiffBump.support_normed_eq] at hh
    simpa only [mem_ball,dist_zero_right] using hh
  have hq' : q+(0,s) ∈ tsupport φ := by
    have he := tsupport_comp_eq_preimage φ (Homeomorph.addRight (0,s))
    change q ∈ tsupport (φ ∘ (Homeomorph.addRight (0,s))) at hq
    rw [he] at hq
    exact hq
  apply hεΩ
  apply mem_thickening_iff.mpr
  refine ⟨q+(0,s),hq',?_⟩
  have hd : dist q (q+(0,s)) = ‖s‖ := by simp [dist_eq_norm]
  rw [hd]
  exact hsrad.trans hn

#print axioms partial_mollifier_shifted_support_eventually
end TheoremT.Continuum
