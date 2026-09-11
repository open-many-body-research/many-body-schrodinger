import BoundedSmoothMultiplier_v1
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
open MeasureTheory Filter
open scoped ENNReal
namespace TheoremT.Continuum

theorem compact_multiplier_memLp_of_local {N : ℕ} {q : ℝ≥0∞}
    {S : Set (Configuration N)} (hS : MeasurableSet S)
    {χ : Configuration N → ℝ} (hχ : MemLp χ ⊤ volume)
    (hs : Function.support χ ⊆ S) {f : Configuration N → ℂ}
    (hf : MemLp f q (volume.restrict S)) : MemLp (fun x => χ x • f x) q volume := by
  have hi : MemLp (S.indicator f) q volume := (memLp_indicator_iff_restrict hS).mpr hf
  have hm : MemLp (fun x => χ x • (S.indicator f) x) q volume := hi.smul hχ
  have he : (fun x => χ x • (S.indicator f) x)=(fun x => χ x • f x) := by
    funext x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx]
    · have hzero : χ x=0 := by
        by_contra hn
        exact hx (hs hn)
      simp only [hzero,zero_smul]
  rwa [he] at hm

theorem boundedRealMul_memLp_of_local {N : ℕ} {q : ℝ≥0∞}
    {S : Set (Configuration N)} (hS : MeasurableSet S)
    {χ : Configuration N → ℝ} (hχ : MemLp χ ⊤ volume)
    (hs : Function.support χ ⊆ S) {f : SpatialL2 N}
    (hf : MemLp f q (volume.restrict S)) : MemLp (boundedRealMul χ hχ f) q volume :=
  MemLp.ae_eq (boundedRealMul_ae χ hχ f).symm
    (compact_multiplier_memLp_of_local hS hχ hs hf)

#print axioms boundedRealMul_memLp_of_local
end TheoremT.Continuum
