import GrushinFactorialMonomialBound_v1
import SpectatorIterationState_v1
import ActualL2IntegralCauchy_v1

/-! Quantitative restricted L2 control of actual monomial weights from a
squared derivative budget. The actual weighted representatives and finite
norms are constructed; no weighted norm estimate is an input. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_monomial_region_budget_bound
    {Ω : Set (Space (Fin 3))} (hΩ : MeasurableSet Ω)
    {S W : ℝ} (hS : 1 ≤ S) (hΩS : ∀ p ∈ Ω, ‖p.1‖ ≤ S)
    {f : Space (Fin 3) → ℂ} (hf : RegionL2Budget f Ω W)
    (γ : Fin 4 → ℕ) (hγ : (∑ i, γ i) ≤ 2) :
    MemLp (fun p => factorialYMonomial γ p.1 • f p) 2 (volume.restrict Ω) ∧
    (eLpNorm (fun p => factorialYMonomial γ p.1 • f p) 2 (volume.restrict Ω)).toReal ≤
      S^2*Real.sqrt W ∧
    ∃ U : Lp ℂ 2 (volume.restrict Ω),
      U =ᵐ[volume.restrict Ω] (fun p => factorialYMonomial γ p.1 • f p) ∧
      ‖U‖ ≤ S^2*Real.sqrt W := by
  let g := fun p : Space (Fin 3) => factorialYMonomial γ p.1 • f p
  have hb : ∀ᵐ p ∂volume.restrict Ω, ‖g p‖ ≤ S^2*‖f p‖ := by
    filter_upwards [ae_restrict_mem hΩ] with p hp
    have hmon : |factorialYMonomial γ p.1| ≤ S^2 := by
      simpa only [pow_zero,mul_one] using
        factorialYMonomial_radial_bound γ 0 (Nat.zero_le _) hγ S hS p.1 (hΩS p hp)
    simpa only [g,norm_smul,Real.norm_eq_abs] using
      mul_le_mul_of_nonneg_right hmon (norm_nonneg (f p))
  have hgm : AEStronglyMeasurable g (volume.restrict Ω) :=
    (((factorialYMonomial_continuous γ).comp continuous_fst).aestronglyMeasurable).smul
      hf.1.aestronglyMeasurable
  have hg : MemLp g 2 (volume.restrict Ω) := hf.1.of_le_mul hgm hb
  let U : Lp ℂ 2 (volume.restrict Ω) := hg.toLp g
  let V : Lp ℂ 2 (volume.restrict Ω) := hf.1.toLp f
  have hU : U =ᵐ[volume.restrict Ω] g := hg.coeFn_toLp
  have hV : V =ᵐ[volume.restrict Ω] f := hf.1.coeFn_toLp
  have hnorm : ‖U‖ ≤ S^2*‖V‖ := by
    apply Lp.norm_le_mul_norm_of_ae_le_mul
    filter_upwards [hU,hV,hb] with p hp hq hr
    rwa [hp,hq]
  have hW : 0 ≤ W := (integral_nonneg (fun _ => sq_nonneg _)).trans hf.2
  have hv2 : ‖V‖^2 ≤ W := by
    rw [actual_l2_toLp_norm_sq_integral]
    exact hf.2
  have hv : ‖V‖ ≤ Real.sqrt W := by
    nlinarith [Real.sq_sqrt hW,Real.sqrt_nonneg W,norm_nonneg V]
  have hn : ‖U‖ ≤ S^2*Real.sqrt W :=
    hnorm.trans (mul_le_mul_of_nonneg_left hv (sq_nonneg S))
  refine ⟨hg,?_,U,hU,hn⟩
  simpa only [U,Lp.norm_toLp] using hn

end TheoremT.Continuum.WeakGrushin
