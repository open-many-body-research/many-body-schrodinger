import CompactWeakDirectionalEnergy_v1
import ProductWeakDirectionalLift_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem productEuclideanLift_ae_support
    {f : Lp ℂ 2 (volume : Measure (Y × T))} {K : Set (Y × T)}
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    ∀ᵐ q ∂volume, q ∉ (WithLp.toLp 2 '' K) → productEuclideanLift f q = 0 := by
  filter_upwards [productEuclideanLift_ae f,
    (WithLp.volume_preserving_ofLp Y T).quasiMeasurePreserving.ae hs] with q hq hp
  intro hn
  rw [hq]
  apply hp
  intro hk
  exact hn ⟨q.ofLp,hk,by simp⟩

theorem product_compact_weak_directional_second_energy
    {f d e : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (hd : WeakProductL2Directional f d v) (he : WeakProductL2Directional d e v)
    {K : Set (Y × T)} (hK : IsCompact K) (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    ‖d‖^2 = -inner ℝ f e := by
  let L : Lp ℂ 2 (volume : Measure (Y × T)) →ₗᵢ[ℝ]
      Lp ℂ 2 (volume : Measure (WithLp 2 (Y × T))) :=
    { toLinearMap := productEuclideanLift.toLinearMap.restrictScalars ℝ
      norm_map' := productEuclideanLift.norm_map }
  have hK' : IsCompact (WithLp.toLp 2 '' K) :=
    hK.image (WithLp.prodContinuousLinearEquiv 2 ℝ Y T).symm.continuous
  have h := compact_weak_directional_second_energy
    (weakL2Directional_productEuclideanLift hd)
    (weakL2Directional_productEuclideanLift he) hK' (productEuclideanLift_ae_support hs)
  change ‖L d‖^2 = -inner ℝ (L f) (L e) at h
  simpa only [L.norm_map,L.inner_map_map] using h

theorem product_compact_weak_directional_half_square_bound
    {f d e : Lp ℂ 2 (volume : Measure (Y × T))} {v : Y × T}
    (hd : WeakProductL2Directional f d v) (he : WeakProductL2Directional d e v)
    {K : Set (Y × T)} (hK : IsCompact K) (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    ‖d‖^2 ≤ (‖f‖^2+‖e‖^2)/2 := by
  rw [product_compact_weak_directional_second_energy hd he hK hs]
  have h := (neg_le_abs (inner ℝ f e)).trans (abs_real_inner_le_norm f e)
  nlinarith [sq_nonneg (‖f‖-‖e‖)]

#print axioms product_compact_weak_directional_second_energy
#print axioms product_compact_weak_directional_half_square_bound
end TheoremT.Continuum
