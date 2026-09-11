import SmoothCompactPrimitive_v1
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Order.Compact

/-! Actual smooth test primitives stay inside the positive half-line. -/
noncomputable section
open MeasureTheory Set Filter
open scoped Topology ContDiff
namespace TheoremT.OneDimensional

theorem halfline_test_primitive (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hcompact : HasCompactSupport f) (hs : tsupport f ⊆ Ioi (0 : ℝ))
    (hz : ∫ x, f x = 0) :
    ∃ F : ℝ → ℝ, ContDiff ℝ ∞ F ∧ HasCompactSupport F ∧
      tsupport F ⊆ Ioi (0 : ℝ) ∧ deriv F = f := by
  let K : Set ℝ := tsupport f ∪ {1}
  have hK : IsCompact K := hcompact.union isCompact_singleton
  have hne : K.Nonempty := ⟨1,Or.inr (by simp)⟩
  have hpos : ∀ x ∈ K, 0 < x := by
    intro x hx
    rcases hx with hx | hx
    · exact hs hx
    · simpa only [Set.mem_singleton_iff] using hx ▸ (by norm_num : (0 : ℝ) < 1)
  obtain ⟨m,hm⟩ := hK.exists_isLeast hne
  obtain ⟨M,hM⟩ := hK.exists_isGreatest hne
  have hm0 := hpos m hm.1
  have hmM : m ≤ M := hm.2 hM.1
  have hab : m/2 < M+1 := by linarith
  have hfs : Function.support f ⊆ Ioo (m/2) (M+1) := by
    intro x hx
    have hxK : x ∈ K := Or.inl (subset_tsupport f hx)
    constructor
    · have hmx := hm.2 hxK
      linarith
    · have hxM := hM.2 hxK
      linarith
  obtain ⟨F,hF,hFc,hFs,hFd⟩ := smooth_compact_primitive f hf (m/2) (M+1) hab hfs hz
  refine ⟨F,hF,hFc,?_,hFd⟩
  intro x hx
  have hmx := (hFs hx).1
  change 0 < x
  linarith

theorem exists_halfline_unit_test :
    ∃ η : ℝ → ℝ, ContDiff ℝ ∞ η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Ioi (0 : ℝ) ∧ ∫ x, η x = 1 := by
  let b : ContDiffBump (1 : ℝ) :=
    ⟨1/4,1/2,by norm_num,by norm_num⟩
  refine ⟨b.normed volume,b.contDiff_normed,b.hasCompactSupport_normed,?_,b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  intro x hx
  have hd : |x-1| ≤ (1/2 : ℝ) := by
    simpa [Metric.mem_closedBall,Real.dist_eq,b] using hx
  have hlo := (abs_le.mp hd).1
  change 0 < x
  linarith

#print axioms halfline_test_primitive
#print axioms exists_halfline_unit_test
end TheoremT.OneDimensional
