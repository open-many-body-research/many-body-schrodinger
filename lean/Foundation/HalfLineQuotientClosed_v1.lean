import HalfLineCoreDensity_v1
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Multiplication by the actual reciprocal coordinate has a closed L² graph.
The proof takes nested almost-everywhere convergent subsequences; no boundedness
of the multiplier, endpoint value, or Sobolev trace is assumed. -/
noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

theorem quotient_of_tendsto {f g : ℕ → E} {f₀ g₀ : E}
    (hf : Tendsto f atTop (𝓝 f₀)) (hg : Tendsto g atTop (𝓝 g₀))
    (h : ∀ n, (g n : ℝ → ℂ) =ᵐ[μ] fun x => x⁻¹ • f n x) :
    (g₀ : ℝ → ℂ) =ᵐ[μ] fun x => x⁻¹ • f₀ x := by
  obtain ⟨s, hs, hfs⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨t, ht, hgt⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hg.comp hs.tendsto_atTop)).exists_seq_tendsto_ae
  filter_upwards [hfs, hgt, ae_all_iff.mpr h] with x hfx hgx hx
  have hm := (hfx.comp ht.tendsto_atTop).const_smul (x⁻¹ : ℝ)
  have he : (fun n => g (s (t n)) x) = (fun n => x⁻¹ • f (s (t n)) x) :=
    funext fun n => hx (s (t n))
  simp only [Function.comp_apply] at hgx hm
  rw [← he] at hm
  exact tendsto_nhds_unique hgx hm

#print axioms quotient_of_tendsto
end TheoremT.HalfLine
