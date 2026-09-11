import GenericCompactH2Approximation_v1
import CompactInnerCoordinate_v1
import Mathlib.MeasureTheory.Function.L2Space

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem compact_weak_directional_second_energy
    {f d e : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hd : WeakL2Directional f d v) (he : WeakL2Directional d e v)
    {K : Set E} (hK : IsCompact K) (hs : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ‖d‖^2 = -inner ℝ f e := by
  obtain ⟨R,hR⟩ := hK.exists_bound_of_continuousOn (continuous_id : Continuous (fun x : E => x)).continuousOn
  have hsR : ∀ᵐ x ∂volume, R < ‖x‖ → f x = 0 := by
    filter_upwards [hs] with x hx hxr
    exact hx (fun hxK => (not_lt_of_ge (hR x hxK)) hxr)
  have hn (n : ℕ) : ‖GenericMollifier.mollifyLp n d‖^2 =
      -inner ℝ (GenericMollifier.mollifyLp n f) (GenericMollifier.mollifyLp n e) := by
    let u := GenericMollifier.mollify (GenericMollifier.mollifierKernel n) f
    have hu : ContDiff ℝ ∞ u := GenericMollifier.mollify_contDiff _
      (GenericMollifier.mollifierKernel_contDiff n) (GenericMollifier.mollifierKernel_hasCompactSupport n) f
    have hc : HasCompactSupport u := GenericMollifier.mollify_compact_of_ae_support hsR n
    have hi := compact_directional_inner_ibp (μ := volume) (w := fun x => fderiv ℝ u x v) hu
      ((hu.fderiv_right (by simp)).clm_apply contDiff_const) hc v
    have hf := GenericMollifier.mollifyLp_ae n f
    have hD := GenericMollifier.mollifyLp_directional_ae hd n
    have hE := GenericMollifier.mollifyLp_second_directional_ae hd he n
    have hl : ‖GenericMollifier.mollifyLp n d‖^2 =
        ∫ x, inner ℝ (fderiv ℝ u x v) (fderiv ℝ u x v) := by
      rw [← real_inner_self_eq_norm_sq,L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hD] with x hx
      rw [hx]
    have hr : inner ℝ (GenericMollifier.mollifyLp n f) (GenericMollifier.mollifyLp n e) =
        ∫ x, inner ℝ (u x) (fderiv ℝ (fun y => fderiv ℝ u y v) x v) := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf,hE] with x hx hy
      rw [hx,hy]
    rw [hl,hr]
    linarith
  have hl := (GenericMollifier.mollifyLp_tendsto d).norm.pow 2
  have hr := ((GenericMollifier.mollifyLp_tendsto f).inner (𝕜 := ℝ)
    (GenericMollifier.mollifyLp_tendsto e)).neg
  exact tendsto_nhds_unique hl (hr.congr (fun n => (hn n).symm))

theorem compact_weak_directional_interpolation
    {f d e : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hd : WeakL2Directional f d v) (he : WeakL2Directional d e v)
    {K : Set E} (hK : IsCompact K) (hs : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ‖d‖^2 ≤ ‖f‖*‖e‖ := by
  rw [compact_weak_directional_second_energy hd he hK hs]
  exact (neg_le_abs _).trans (abs_real_inner_le_norm _ _)

theorem compact_weak_directional_half_square_bound
    {f d e : Lp ℂ 2 (volume : Measure E)} {v : E}
    (hd : WeakL2Directional f d v) (he : WeakL2Directional d e v)
    {K : Set E} (hK : IsCompact K) (hs : ∀ᵐ x ∂volume, x ∉ K → f x = 0) :
    ‖d‖^2 ≤ (‖f‖^2+‖e‖^2)/2 := by
  have h := compact_weak_directional_interpolation hd he hK hs
  nlinarith [sq_nonneg (‖f‖-‖e‖)]

#print axioms compact_weak_directional_second_energy
#print axioms compact_weak_directional_half_square_bound
end TheoremT.Continuum
