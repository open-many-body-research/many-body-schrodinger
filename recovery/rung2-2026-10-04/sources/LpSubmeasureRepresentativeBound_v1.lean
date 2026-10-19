import Mathlib.MeasureTheory.Function.L2Space

/-! Restricting a genuine L2 representative to a smaller measure preserves
membership and decreases its norm, including after an almost-everywhere
change of representative. No regularity or density premise is needed. -/
noncomputable section
open MeasureTheory Filter

namespace TheoremT.Continuum

variable {X : Type*} [MeasurableSpace X] {μ ν : Measure X}

theorem lp_submeasure_representative_bound (hνμ : ν ≤ μ)
    (f : Lp ℂ 2 μ) (g : X → ℂ) (hfg : (f : X → ℂ) =ᵐ[ν] g) :
    MemLp g 2 ν ∧ (eLpNorm g 2 ν).toReal ≤ ‖f‖ := by
  have hfm : MemLp (f : X → ℂ) 2 ν := (Lp.memLp f).mono_measure hνμ
  refine ⟨hfm.ae_eq hfg, ?_⟩
  rw [← eLpNorm_congr_ae hfg, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.memLp f).2.ne (eLpNorm_mono_measure _ hνμ)

theorem lp_submeasure_representative_exists (hνμ : ν ≤ μ)
    (f : Lp ℂ 2 μ) (g : X → ℂ) (hfg : (f : X → ℂ) =ᵐ[ν] g) :
    ∃ u : Lp ℂ 2 ν, (u : X → ℂ) =ᵐ[ν] g ∧ ‖u‖ ≤ ‖f‖ := by
  obtain ⟨hm, hb⟩ := lp_submeasure_representative_bound hνμ f g hfg
  refine ⟨hm.toLp g, hm.coeFn_toLp, ?_⟩
  simpa only [Lp.norm_toLp] using hb

end TheoremT.Continuum
