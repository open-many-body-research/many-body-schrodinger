import CompactSlabPoincare_v1
import ProductCompactH2Approximation_v1
import WeakGrushinJetLimits_v1

/-! Slab Poincare inequality for actual compactly supported weak H2 inputs.
First pass the radius-free oscillator inequality through strong L2 approximation
with one common compact support. Only afterward apply the slab bound to the
actual limiting function. No radius bound is imposed on the approximants. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_weakH2_oscillator_bound
    (L : Space κ →L[ℝ] ℝ) (v : Space κ) (hLv : L v = 1)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ w, WeakProductL2Directional f (d w) w)
    (he : ∀ w z, WeakProductL2Directional (d w) (e w z) z)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) (a : ℝ) :
    a*(∫ p, ‖f p‖^2) ≤
      (∫ p, ‖d v p‖^2) + a^2*(∫ p, ‖L p • f p‖^2) := by
  letI := euclidean_product_volume_isAddHaar (ι := Fin 4) (κ := κ)
  obtain ⟨S,hS,hKS,u,g,dg,eg,hu,huc,hus,hgu,hdu,heu,hgconv,hdconv,heconv⟩ :=
    product_compact_weakH2_uniform_support_approximation d e hd he hK hs
  have hgs (n : ℕ) : ∀ᵐ p ∂volume, p ∉ S → g n p = 0 := by
    filter_upwards [hgu n] with p hp hnot
    rw [hp]
    apply image_eq_zero_of_notMem_tsupport
    exact fun hm => hnot (hus n hm)
  have hfn := l2_integral_norm_sq_tendsto hgconv
  have hdn := l2_integral_norm_sq_tendsto (hdconv v)
  have hwn := compact_support_weight_norm_sq_tendsto hS L L.continuous hgconv hgs
  have hb (n : ℕ) : a*(∫ p, ‖g n p‖^2) ≤
      (∫ p, ‖dg n v p‖^2) + a^2*(∫ p, ‖L p • g n p‖^2) := by
    have hfq : (∫ p, ‖g n p‖^2) = ∫ p, ‖u n p‖^2 := by
      apply integral_congr_ae
      filter_upwards [hgu n] with p hp
      rw [hp]
    have hdq : (∫ p, ‖dg n v p‖^2) = ∫ p, ‖fderiv ℝ (u n) p v‖^2 := by
      apply integral_congr_ae
      filter_upwards [hdu n v] with p hp
      rw [hp]
    have hwq : (∫ p, ‖L p • g n p‖^2) = ∫ p, ‖L p • u n p‖^2 := by
      apply integral_congr_ae
      filter_upwards [hgu n] with p hp
      rw [hp]
    rw [hfq, hdq, hwq]
    exact compact_complex_oscillator_directional_bound (μ := volume)
      L v hLv ((hu n).of_le (by simp)) (huc n) a
  exact le_of_tendsto_of_tendsto' (hfn.const_mul a)
    (hdn.add (hwn.const_mul (a^2))) hb

theorem compact_l2_slab_weight_integral_bound
    (L : Space κ →L[ℝ] ℝ) {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    {R : ℝ} (hR : 0 ≤ R)
    (hslab : ∀ᵐ p ∂volume, f p ≠ 0 → |L p| ≤ R) :
    (∫ p, ‖L p • f p‖^2) ≤ R^2*(∫ p, ‖f p‖^2) := by
  have hi : Integrable (fun p => ‖f p‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  have hwm := compact_support_weight_memLp hK L L.continuous f hs
  have hw : Integrable (fun p => ‖L p • f p‖^2) volume :=
    (memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable).mp hwm
  calc
    (∫ p, ‖L p • f p‖^2) ≤ ∫ p, R^2*‖f p‖^2 := by
      apply integral_mono_ae hw (hi.const_mul _)
      filter_upwards [hslab] with p hp
      by_cases hz : f p = 0
      · simp [hz]
      · rw [norm_smul, mul_pow, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ (abs_nonneg _) (hp hz) 2) (sq_nonneg _)
    _ = R^2*(∫ p, ‖f p‖^2) := integral_const_mul _ _

theorem compact_weakH2_slab_poincare_integral
    (L : Space κ →L[ℝ] ℝ) (v : Space κ) (hLv : L v = 1)
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ w, WeakProductL2Directional f (d w) w)
    (he : ∀ w z, WeakProductL2Directional (d w) (e w z) z)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    {R : ℝ} (hR : 0 < R)
    (hslab : ∀ᵐ p ∂volume, f p ≠ 0 → |L p| ≤ R) :
    (∫ p, ‖f p‖^2) ≤ 4*R^2*(∫ p, ‖d v p‖^2) := by
  have hw := compact_l2_slab_weight_integral_bound L hK hs hR.le hslab
  have ho := compact_weakH2_oscillator_bound L v hLv d e hd he hK hs ((2*R^2)⁻¹)
  have ho2 := ho.trans (add_le_add_right
    (mul_le_mul_of_nonneg_left hw (sq_nonneg ((2*R^2)⁻¹))) _)
  have hm := mul_le_mul_of_nonneg_left ho2 (show 0 ≤ 2*R^2 from by positivity)
  have hRn : R ≠ 0 := ne_of_gt hR
  have hl : (2*R^2)*((2*R^2)⁻¹*(∫ p, ‖f p‖^2)) =
      (∫ p, ‖f p‖^2) := by field_simp
  have hr : (2*R^2)*((∫ p, ‖d v p‖^2)+
      ((2*R^2)⁻¹)^2*(R^2*(∫ p, ‖f p‖^2))) =
      (2*R^2)*(∫ p, ‖d v p‖^2)+(∫ p, ‖f p‖^2)/2 := by
    field_simp
    <;> ring
  rw [hl, hr] at hm
  linarith

theorem compact_weakH2_y_slab_poincare_integral
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ w, WeakProductL2Directional f (d w) w)
    (he : ∀ w z, WeakProductL2Directional (d w) (e w z) z)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) (i : Fin 4)
    {R : ℝ} (hR : 0 < R)
    (hslab : ∀ᵐ p ∂volume, f p ≠ 0 → |p.1 i| ≤ R) :
    (∫ p, ‖f p‖^2) ≤ 4*R^2*(∫ p, ‖d (yDir i) p‖^2) := by
  let L : Space κ →L[ℝ] ℝ :=
    (EuclideanSpace.proj i).comp (ContinuousLinearMap.fst ℝ _ _)
  have hLv : L (yDir i) = 1 := by simp [L, yDir, oscillatorBasis]
  exact compact_weakH2_slab_poincare_integral L (yDir i) hLv d e hd he hK hs hR hslab

theorem compact_weakH2_y_slab_poincare_on_compact
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ w, WeakProductL2Directional f (d w) w)
    (he : ∀ w z, WeakProductL2Directional (d w) (e w z) z)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) (i : Fin 4)
    {R : ℝ} (hR : 0 < R) (hslab : ∀ p ∈ K, |p.1 i| ≤ R) :
    (∫ p, ‖f p‖^2) ≤ 4*R^2*(∫ p, ‖d (yDir i) p‖^2) := by
  apply compact_weakH2_y_slab_poincare_integral d e hd he hK hs i hR
  filter_upwards [hs] with p hp hne
  exact hslab p (by by_contra hnot; exact hne (hp hnot))

end TheoremT.Continuum.WeakGrushin
