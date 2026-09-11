import GrushinLocalPotentialL2_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_continuousOn_locallyL2 {Ω : Set (Y × T)} {f : Y × T → ℂ}
    (hf : ContinuousOn f Ω) : ProductLocallyL2On f Ω := by
  intro K hK hKΩ
  have hfK := hf.mono hKΩ
  obtain ⟨C,hC⟩ := hK.exists_bound_of_continuousOn hfK
  have ht : MemLp f ⊤ (volume.restrict K) := by
    apply memLp_top_of_bound (hfK.aestronglyMeasurable hK.measurableSet) C
    filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
    exact hC p hp
  haveI : IsFiniteMeasure (volume.restrict K) := ⟨by
    rw [Measure.restrict_apply_univ]
    exact hK.measure_lt_top⟩
  exact ht.mono_exponent (by simp)

#print axioms product_continuousOn_locallyL2
end TheoremT.Continuum
