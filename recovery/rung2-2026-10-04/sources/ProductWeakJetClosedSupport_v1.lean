import ProductWeakEllipticGain_v1
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Actual weak directional derivatives preserve a closed support set.
This uses local compact-test uniqueness directly, so it does not enlarge
the original support to the larger compact set used by mollification. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem weakProductL2Directional_closed_support
    {f d : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (hd : WeakProductL2Directional f d v) {K : Set (Y × T)} (hK : IsClosed K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    ∀ᵐ p ∂volume, p ∉ K → d p = 0 := by
  have hdli := (Lp.memLp d).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  apply hK.isOpen_compl.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hdli.locallyIntegrableOn Kᶜ)
  intro φ hφ hc hφK
  rw [hd φ hφ hc]
  suffices hz : (∫ p, fderiv ℝ φ p v • f p) = 0 by rw [hz,neg_zero]
  apply integral_eq_zero_of_ae
  filter_upwards [hs] with p hp
  by_cases hk : p ∈ K
  · have hz : fderiv ℝ φ p v = 0 := by
      apply image_eq_zero_of_notMem_tsupport (f := fun x => fderiv ℝ φ x v)
      intro hm
      exact (hφK ((tsupport_fderiv_apply_subset ℝ v) hm)) hk
    simp only [hz,zero_smul,Pi.zero_apply]
  · simp only [hp hk,smul_zero,Pi.zero_apply]

theorem weakProductL2Second_closed_support
    {f d e : Lp ℂ 2 (volume : Measure (Y × T))} {v w : Y × T}
    (hd : WeakProductL2Directional f d v) (he : WeakProductL2Directional d e w)
    {K : Set (Y × T)} (hK : IsClosed K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    ∀ᵐ p ∂volume, p ∉ K → e p = 0 :=
  weakProductL2Directional_closed_support he hK
    (weakProductL2Directional_closed_support hd hK hs)

end TheoremT.Continuum
