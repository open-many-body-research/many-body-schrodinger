import LpSupportClosed_v1
import Mathlib.Analysis.Calculus.FDeriv.Extend

/-! Support of actual L2 representatives of classical directional derivatives,
and preservation of that support in a strong L2 limit. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] {μ : Measure E}

theorem lp_ae_zero_off_of_directional_support
    {u : E → ℂ} {K : Set E} (hu : tsupport u ⊆ K)
    {g : Lp ℂ 2 μ} {v : E}
    (hg : (g : E → ℂ) =ᵐ[μ] (fun x => fderiv ℝ u x v)) :
    ∀ᵐ x ∂μ, x ∉ K → g x = 0 := by
  filter_upwards [hg] with x hx ho
  rw [hx]
  apply image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ u y v)
  intro hd
  exact ho (hu ((tsupport_fderiv_apply_subset ℝ v) hd))

theorem lp_ae_zero_off_of_second_directional_support
    {u : E → ℂ} {K : Set E} (hu : tsupport u ⊆ K)
    {g : Lp ℂ 2 μ} {v w : E}
    (hg : (g : E → ℂ) =ᵐ[μ]
      (fun x => fderiv ℝ (fun z => fderiv ℝ u z v) x w)) :
    ∀ᵐ x ∂μ, x ∉ K → g x = 0 :=
  lp_ae_zero_off_of_directional_support ((tsupport_fderiv_apply_subset ℝ v).trans hu) hg

theorem lp_directional_support_of_tendsto
    {u : ℕ → E → ℂ} {K : Set E} (hK : MeasurableSet K)
    (hu : ∀ n, tsupport (u n) ⊆ K)
    {g : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ} {v : E}
    (hg : ∀ n, (g n : E → ℂ) =ᵐ[μ] (fun x => fderiv ℝ (u n) x v))
    (hlim : Tendsto g atTop (𝓝 f)) :
    ∀ᵐ x ∂μ, x ∉ K → f x = 0 :=
  lp_ae_zero_on_of_tendsto hK.compl hlim
    (fun n => lp_ae_zero_off_of_directional_support (hu n) (hg n))

theorem lp_second_directional_support_of_tendsto
    {u : ℕ → E → ℂ} {K : Set E} (hK : MeasurableSet K)
    (hu : ∀ n, tsupport (u n) ⊆ K)
    {g : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ} {v w : E}
    (hg : ∀ n, (g n : E → ℂ) =ᵐ[μ]
      (fun x => fderiv ℝ (fun z => fderiv ℝ (u n) z v) x w))
    (hlim : Tendsto g atTop (𝓝 f)) :
    ∀ᵐ x ∂μ, x ∉ K → f x = 0 :=
  lp_ae_zero_on_of_tendsto hK.compl hlim
    (fun n => lp_ae_zero_off_of_second_directional_support (hu n) (hg n))

end TheoremT.Continuum
