import GenericWeakWordMollification_v1
import ProductWeakDirectionalLift_v1

/-! Finite weak coordinate-word mollification on the ordinary product with
its maximum norm and actual product Lebesgue measure. The explicit pulled-back
generic word fields obey genuine product fderiv identities. No inner-product
structure on the ordinary product is assumed or introduced. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]
variable {ι : Type*}

def productMollifiedWord (dirs : ι → Y × T)
    (D : List ι → Lp ℂ 2 (volume : Measure (Y × T))) (n : ℕ) (w : List ι) :
    (Y × T) → ℂ :=
  GenericMollifier.complexDirectionalWordDeriv (fun i => WithLp.toLp 2 (dirs i))
    (GenericMollifier.mollify (GenericMollifier.mollifierKernel n)
      (productEuclideanLift (D []))) w ∘ WithLp.toLp 2

def productMollifiedWordLp
    (D : List ι → Lp ℂ 2 (volume : Measure (Y × T))) (n : ℕ) (w : List ι) :
    Lp ℂ 2 (volume : Measure (Y × T)) :=
  productEuclideanUnlift (GenericMollifier.mollifyLp n (productEuclideanLift (D w)))

theorem productMollifiedWord_contDiff (dirs : ι → Y × T)
    (D : List ι → Lp ℂ 2 (volume : Measure (Y × T))) (n : ℕ) (w : List ι) :
    ContDiff ℝ ∞ (productMollifiedWord dirs D n w) := by
  apply (GenericMollifier.complexDirectionalWordDeriv_contDiff _
    (GenericMollifier.mollify_contDiff _ (GenericMollifier.mollifierKernel_contDiff n)
      (GenericMollifier.mollifierKernel_hasCompactSupport n) _) w).comp
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ Y T).symm.contDiff

theorem productMollifiedWord_directional (dirs : ι → Y × T)
    (D : List ι → Lp ℂ 2 (volume : Measure (Y × T)))
    (n : ℕ) (w : List ι) (i : ι) (p : Y × T) :
    fderiv ℝ (productMollifiedWord dirs D n w) p (dirs i) =
      productMollifiedWord dirs D n (i :: w) p := by
  exact productEuclideanUnlift_directional_chain
    (GenericMollifier.complexDirectionalWordDeriv_contDiff _
      (GenericMollifier.mollify_contDiff _ (GenericMollifier.mollifierKernel_contDiff n)
        (GenericMollifier.mollifierKernel_hasCompactSupport n) _) w) p (dirs i)

theorem productMollifiedWordLp_ae (dirs : ι → Y × T)
    (D : List ι → Lp ℂ 2 (volume : Measure (Y × T))) {m : ℕ}
    (hD : ∀ w i, w.length < m →
      WeakProductL2Directional (D w) (D (i :: w)) (dirs i))
    (n : ℕ) (w : List ι) (hw : w.length ≤ m) :
    (productMollifiedWordLp D n w : Y × T → ℂ) =ᵐ[volume]
      productMollifiedWord dirs D n w := by
  have hDE (v : List ι) (i : ι) (hv : v.length < m) :
      WeakL2Directional (productEuclideanLift (D v))
        (productEuclideanLift (D (i :: v))) (WithLp.toLp 2 (dirs i)) :=
    weakL2Directional_productEuclideanLift (hD v i hv)
  have he := GenericMollifier.mollifyLp_word_ae
    (fun i => WithLp.toLp 2 (dirs i)) (fun v => productEuclideanLift (D v)) hDE n w hw
  filter_upwards [productEuclideanUnlift_ae
    (GenericMollifier.mollifyLp n (productEuclideanLift (D w))),
    (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae he] with p hp hq
  exact hp.trans hq

theorem productMollifiedWordLp_tendsto
    (D : List ι → Lp ℂ 2 (volume : Measure (Y × T))) (w : List ι) :
    Tendsto (fun n => productMollifiedWordLp D n w) atTop (𝓝 (D w)) := by
  simpa only [productMollifiedWordLp,Function.comp_def,productEuclideanUnlift_lift] using
    (productEuclideanUnlift.continuous.tendsto _).comp
      (GenericMollifier.mollifyLp_tendsto (productEuclideanLift (D w)))

theorem productMollifiedWordLp_norm_le
    (D : List ι → Lp ℂ 2 (volume : Measure (Y × T))) (n : ℕ) (w : List ι) :
    ‖productMollifiedWordLp D n w‖ ≤ ‖D w‖ := by
  simpa only [productMollifiedWordLp,LinearIsometry.norm_map] using
    GenericMollifier.mollifyLp_norm_le n (productEuclideanLift (D w))

end TheoremT.Continuum
