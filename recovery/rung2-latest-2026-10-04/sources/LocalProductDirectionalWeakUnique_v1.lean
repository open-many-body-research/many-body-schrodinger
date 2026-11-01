import LocalProductDirectionalWeakLinear_v1
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-! Uniqueness of genuine local weak derivative representatives on an open
set. Local L2 gives local integrability; the conclusion is local almost
-everywhere equality, not pointwise equality of arbitrarily chosen functions.
-/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem productLocallyL2On_locallyIntegrableOn
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {f : Y × T → ℂ}
    (hf : ProductLocallyL2On f Ω) : LocallyIntegrableOn f Ω volume := by
  apply (locallyIntegrableOn_iff hΩ.isLocallyClosed).mpr
  intro K hKΩ hK
  letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_lt_top.ne
  exact (hf K hK hKΩ).integrable (by norm_num)

theorem ProductLocalWeakDirectional.unique
    {Ω : Set (Y × T)} (hΩ : IsOpen Ω) {f d e : Y × T → ℂ} {v : Y × T}
    (hd : ProductLocalWeakDirectional Ω f d v)
    (he : ProductLocalWeakDirectional Ω f e v) :
    ∀ᵐ p ∂volume, p ∈ Ω → d p = e p := by
  have hloc : LocallyIntegrableOn (fun p => d p - e p) Ω volume :=
    (productLocallyL2On_locallyIntegrableOn hΩ hd.2.1).sub
      (productLocallyL2On_locallyIntegrableOn hΩ he.2.1)
  have hz := hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc
    (fun φ hφ hc hs => by
      have hi := (hd.test_integrable hφ hc hs).1
      have hj := (he.test_integrable hφ hc hs).1
      simp only [smul_sub]
      rw [integral_sub hi hj,hd.2.2 φ hφ hc hs,he.2.2 φ hφ hc hs,sub_self])
  filter_upwards [hz] with p hp hmem
  exact sub_eq_zero.mp (hp hmem)

#print axioms productLocallyL2On_locallyIntegrableOn
#print axioms ProductLocalWeakDirectional.unique
end TheoremT.Continuum
