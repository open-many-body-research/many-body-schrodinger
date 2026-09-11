import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Complex.Basic

noncomputable section
open MeasureTheory Filter Set
namespace TheoremT.Continuum

theorem continuous_norm_bound_of_ae {X E : Type*} [TopologicalSpace X]
    [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) [μ.IsOpenPosMeasure]
    {u : X → E} (hu : Continuous u) {C : ℝ} (hC : ∀ᵐ x ∂μ, ‖u x‖ ≤ C) :
    ∀ x, ‖u x‖ ≤ C := by
  have hs : IsClosed {x | ‖u x‖ ≤ C} := isClosed_le hu.norm continuous_const
  have he : {x | ‖u x‖ ≤ C}=univ := (hs.ae_eq_univ_iff_eq (μ := μ)).mp (by
    filter_upwards [hC] with x hx
    exact propext (iff_true_intro hx))
  intro x
  have hx : x ∈ {x | ‖u x‖ ≤ C} := he.symm ▸ mem_univ x
  exact hx

#print axioms continuous_norm_bound_of_ae
end TheoremT.Continuum
