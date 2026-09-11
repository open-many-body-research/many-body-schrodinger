import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSpace.Complete

noncomputable section
open MeasureTheory Filter
open scoped Topology ENNReal
namespace TheoremT.Continuum

theorem l2_local_equality_closed {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {S : Set X}
    {F G : ℕ → Lp E 2 μ} {f g : Lp E 2 μ}
    (hF : Tendsto F atTop (𝓝 f)) (hG : Tendsto G atTop (𝓝 g))
    (he : ∀ n, ∀ᵐ x ∂μ, x ∈ S → F n x=G n x) :
    ∀ᵐ x ∂μ, x ∈ S → f x=g x := by
  obtain ⟨a, ha, hfa⟩ := (tendstoInMeasure_of_tendsto_Lp hF).exists_seq_tendsto_ae
  obtain ⟨b, hb, hgb⟩ := (tendstoInMeasure_of_tendsto_Lp (hG.comp ha.tendsto_atTop)).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, x ∈ S → F n x=G n x := by
    rw [ae_all_iff]
    exact he
  filter_upwards [hfa,hgb,hall] with x hfx hgx hex
  intro hx
  have hl := hfx.comp hb.tendsto_atTop
  change Tendsto (fun n => F (a (b n)) x) atTop (𝓝 (f x)) at hl
  have heq : (fun n => F (a (b n)) x)=(fun n => G (a (b n)) x) := by
    funext n
    exact hex _ hx
  rw [heq] at hl
  exact tendsto_nhds_unique hl hgx

#print axioms l2_local_equality_closed
end TheoremT.Continuum
