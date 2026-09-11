import GenericCompactH2Approximation_v1
import ProductWeakDirectionalLift_v1

/-! Actual weak H2 compact approximation on the ordinary product with its
maximum norm and product Lebesgue measure. An exact measure-preserving WithLp 2
coordinate transport supplies one fixed larger compact support set. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_compact_weakH2_uniform_support_approximation
    {f : Lp ℂ 2 (volume : Measure (Y × T))}
    (d : (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)))
    (e : (Y × T) → (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Y × T)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    ∃ L : Set (Y × T), IsCompact L ∧ K ⊆ L ∧
      ∃ u : ℕ → (Y × T) → ℂ,
      ∃ g : ℕ → Lp ℂ 2 (volume : Measure (Y × T)),
      ∃ dg : ℕ → (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      ∃ eg : ℕ → (Y × T) → (Y × T) → Lp ℂ 2 (volume : Measure (Y × T)),
      (∀ n, ContDiff ℝ ∞ (u n)) ∧
      (∀ n, HasCompactSupport (u n)) ∧
      (∀ n, tsupport (u n) ⊆ L) ∧
      (∀ n, (g n : (Y × T) → ℂ) =ᵐ[volume] u n) ∧
      (∀ n v, (dg n v : (Y × T) → ℂ) =ᵐ[volume]
        (fun p => fderiv ℝ (u n) p v)) ∧
      (∀ n v w, (eg n v w : (Y × T) → ℂ) =ᵐ[volume]
        (fun p => fderiv ℝ (fun z => fderiv ℝ (u n) z v) p w)) ∧
      Tendsto g atTop (𝓝 f) ∧
      (∀ v, Tendsto (fun n => dg n v) atTop (𝓝 (d v))) ∧
      (∀ v w, Tendsto (fun n => eg n v w) atTop (𝓝 (e v w))) := by
  let c := WithLp.prodContinuousLinearEquiv 2 ℝ Y T
  have hk : IsCompact (c.symm '' K) := hK.image c.symm.continuous
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall (0 : WithLp 2 (Y × T))
  have hsE : ∀ᵐ q ∂volume, R < ‖q‖ → productEuclideanLift f q = 0 := by
    filter_upwards [productEuclideanLift_ae f,
      (WithLp.volume_preserving_ofLp Y T).quasiMeasurePreserving.ae hs] with q hq hp
    intro hr
    rw [hq]
    apply hp
    intro hm
    have h := hR (show q ∈ c.symm '' K from ⟨q.ofLp, hm, by simp [c]⟩)
    have hn : ‖q‖ ≤ R := by simpa only [mem_closedBall_zero_iff] using h
    exact (not_le_of_gt hr) hn
  have hdE (v : WithLp 2 (Y × T)) :
      WeakL2Directional (productEuclideanLift f) (productEuclideanLift (d v.ofLp)) v := by
    simpa using weakL2Directional_productEuclideanLift (hd v.ofLp)
  have heE (v w : WithLp 2 (Y × T)) :
      WeakL2Directional (productEuclideanLift (d v.ofLp))
        (productEuclideanLift (e v.ofLp w.ofLp)) w := by
    simpa using weakL2Directional_productEuclideanLift (he v.ofLp w.ofLp)
  obtain ⟨u,g,dg,eg,hu,hc,hb,hg,hdg,heg,hgconv,hdconv,heconv⟩ :=
    GenericMollifier.compact_weakH2_uniform_support_approximation
      (fun v => productEuclideanLift (d v.ofLp))
      (fun v w => productEuclideanLift (e v.ofLp w.ofLp)) hdE heE hsE
  let L := K ∪ c '' Metric.closedBall 0 (R+2)
  have hL : IsCompact L := hK.union ((isCompact_closedBall _ _).image c.continuous)
  refine ⟨L,hL,Set.subset_union_left,
    (fun n => u n ∘ WithLp.toLp 2), (fun n => productEuclideanUnlift (g n)),
    (fun n v => productEuclideanUnlift (dg n (WithLp.toLp 2 v))),
    (fun n v w => productEuclideanUnlift (eg n (WithLp.toLp 2 v) (WithLp.toLp 2 w))),
    (fun n => (hu n).comp c.symm.contDiff),
    (fun n => (hc n).comp_homeomorph c.symm.toHomeomorph), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    apply closure_minimal _ hL.isClosed
    intro p hp
    apply Set.mem_union_right
    exact ⟨WithLp.toLp 2 p, hb n (subset_closure hp), rfl⟩
  · intro n
    filter_upwards [productEuclideanUnlift_ae (g n),
      (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae (hg n)] with p hp hq
    exact hp.trans hq
  · intro n v
    filter_upwards [productEuclideanUnlift_ae (dg n (WithLp.toLp 2 v)),
      (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae
        (hdg n (WithLp.toLp 2 v))] with p hp hq
    rw [hp, Function.comp_apply, hq, productEuclideanUnlift_directional_chain (hu n)]
  · intro n v w
    filter_upwards [productEuclideanUnlift_ae (eg n (WithLp.toLp 2 v) (WithLp.toLp 2 w)),
      (WithLp.volume_preserving_toLp Y T).quasiMeasurePreserving.ae
        (heg n (WithLp.toLp 2 v) (WithLp.toLp 2 w))] with p hp hq
    rw [hp, Function.comp_apply, hq, productEuclideanUnlift_second_directional_chain (hu n)]
  · simpa only [Function.comp_def,productEuclideanUnlift_lift] using
      (productEuclideanUnlift.continuous.tendsto _).comp hgconv
  · intro v
    simpa only [Function.comp_def,WithLp.ofLp_toLp,productEuclideanUnlift_lift] using
      (productEuclideanUnlift.continuous.tendsto _).comp (hdconv (WithLp.toLp 2 v))
  · intro v w
    simpa only [Function.comp_def,WithLp.ofLp_toLp,productEuclideanUnlift_lift] using
      (productEuclideanUnlift.continuous.tendsto _).comp
        (heconv (WithLp.toLp 2 v) (WithLp.toLp 2 w))

end TheoremT.Continuum
