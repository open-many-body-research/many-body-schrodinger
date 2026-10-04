import ProductDirectionalWordLeibniz_v1
import FiniteDimSmoothCutoff_v1

/-! Compactly supported genuine local weak directional derivatives globalize
without a boundary term. A smooth test cutoff equal to one near the shared
compact support is constructed, rather than assumed. -/
noncomputable section
open Set MeasureTheory Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum
variable {Y T : Type*}
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y] [FiniteDimensional ℝ Y]
  [MeasurableSpace Y] [BorelSpace Y]
  [NormedAddCommGroup T] [InnerProductSpace ℝ T] [FiniteDimensional ℝ T]
  [MeasurableSpace T] [BorelSpace T]

theorem product_locallyL2_memLp_of_compact_support
    {Ω K : Set (Y × T)} (hK : IsCompact K) (hKO : K ⊆ Ω)
    {f : Y × T → ℂ} (hf : ProductLocallyL2On f Ω)
    (hs : Function.support f ⊆ K) : MemLp f 2 volume := by
  have hi := (memLp_indicator_iff_restrict hK.measurableSet).mpr (hf K hK hKO)
  rwa [Set.indicator_eq_self.mpr hs] at hi

theorem ProductLocalWeakDirectional.global_tests_of_compact_support
    {Ω K : Set (Y × T)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKO : K ⊆ Ω)
    {f g : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f g v)
    (hsf : Function.support f ⊆ K) (hsg : Function.support g ⊆ K) :
    ∀ φ : Y × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, φ p • g p) = -(∫ p, fderiv ℝ φ p v • f p) := by
  obtain ⟨η,hη,hcη,hsη,h1⟩ := finiteDim_compact_exists_smooth_cutoff hK hΩ hKO
  intro φ hφ hcφ
  have ht := hD.2.2 (fun p => η p * φ p) (hη.mul hφ) hcη.mul_right
    (tsupport_mul_subset_left.trans hsη)
  have heL : (fun p => (η p * φ p) • g p) = fun p => φ p • g p := by
    funext p
    by_cases hp : p ∈ K
    · rw [(h1 p hp).eq_of_nhds,one_mul]
    · have hg : g p = 0 := by
        by_contra hn
        exact hp (hsg hn)
      simp [hg]
  have heR : (fun p => fderiv ℝ (fun q => η q * φ q) p v • f p) =
      fun p => fderiv ℝ φ p v • f p := by
    funext p
    by_cases hp : p ∈ K
    · have he : (fun q => η q * φ q) =ᶠ[𝓝 p] φ := by
        filter_upwards [h1 p hp] with q hq
        simp only [hq,one_mul]
      rw [he.fderiv_eq]
    · have hf : f p = 0 := by
        by_contra hn
        exact hp (hsf hn)
      simp [hf]
  rwa [heL,heR] at ht

theorem ProductLocalWeakDirectional.globalize_of_compact_support
    {Ω K : Set (Y × T)} (hΩ : IsOpen Ω) (hK : IsCompact K) (hKO : K ⊆ Ω)
    {f g : Y × T → ℂ} {v : Y × T}
    (hD : ProductLocalWeakDirectional Ω f g v)
    (hsf : Function.support f ⊆ K) (hsg : Function.support g ⊆ K) :
    ∃ F G : Lp ℂ 2 (volume : Measure (Y × T)),
      F =ᵐ[volume] f ∧ G =ᵐ[volume] g ∧ WeakProductL2Directional F G v := by
  have hf := product_locallyL2_memLp_of_compact_support hK hKO hD.1 hsf
  have hg := product_locallyL2_memLp_of_compact_support hK hKO hD.2.1 hsg
  refine ⟨hf.toLp f,hg.toLp g,hf.coeFn_toLp,hg.coeFn_toLp,?_⟩
  intro φ hφ hcφ
  have hL : (∫ p, φ p • hg.toLp g p) = ∫ p, φ p • g p := by
    apply integral_congr_ae
    filter_upwards [hg.coeFn_toLp] with p hp
    rw [hp]
  have hR : (∫ p, fderiv ℝ φ p v • hf.toLp f p) = ∫ p, fderiv ℝ φ p v • f p := by
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp] with p hp
    rw [hp]
  rw [hL,hR]
  exact hD.global_tests_of_compact_support hΩ hK hKO hsf hsg φ hφ hcφ

end TheoremT.Continuum
