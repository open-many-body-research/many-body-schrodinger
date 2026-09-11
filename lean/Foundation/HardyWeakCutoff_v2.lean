import HardyWeakCutoff_v1

noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum

private theorem cutoff_h1_add {N : ℕ} {f g : SpatialL2 N}
    (hf : HasH1 f) (hg : HasH1 g) : HasH1 (f + g) := by
  obtain ⟨df, hf⟩ := hf
  obtain ⟨dg, hg⟩ := hg
  exact ⟨fun k => df k + dg k, fun k => weakPartial_add (hf k) (hg k)⟩

/-- Smooth compact cutoffs preserve every mixed second weak L² derivative. -/
theorem HasH2.cutoff {N : ℕ} {f : SpatialL2 N} (hf : HasH2 f)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ) :
    HasH2 (cutoffMul χ hχ.continuous hcχ f) := by
  obtain ⟨d, hd, hdd⟩ := hf
  have hf1 : HasH1 f := ⟨d, hd⟩
  have hd1 : ∀ k, HasH1 (d k) := by
    intro k
    choose e he using hdd k
    exact ⟨e, he⟩
  have hχd : ∀ k : Coordinate N,
      ContDiff ℝ ∞ (fun x => fderiv ℝ χ x (coordinateVector k)) := by
    intro k
    exact (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞) + 1 ≤ ∞)).clm_apply contDiff_const
  let D : Coordinate N → SpatialL2 N := fun k =>
    cutoffMul χ hχ.continuous hcχ (d k) +
    cutoffMul (fun x => fderiv ℝ χ x (coordinateVector k))
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hcχ.fderiv_apply ℝ (coordinateVector k)) f
  refine ⟨D, ?_, ?_⟩
  · intro k
    exact weakPartial_cutoff (hd k) χ hχ hcχ
  · intro k l
    have hD : HasH1 (D k) := cutoff_h1_add
      ((hd1 k).cutoff χ hχ hcχ)
      (hf1.cutoff _ (hχd k) (hcχ.fderiv_apply ℝ (coordinateVector k)))
    obtain ⟨e, he⟩ := hD
    exact ⟨e l, he l⟩

#print axioms HasH2.cutoff
end TheoremT.Continuum
