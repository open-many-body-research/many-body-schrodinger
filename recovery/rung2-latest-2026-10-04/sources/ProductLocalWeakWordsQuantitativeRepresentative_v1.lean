import ProductSevenMollifierLimits_v1
import ProductCompactAllWeakWords_v1
import ProductCutoffWordPlateau_v1
import SmoothWordBoxQuantitativeRepresentative_v1

/-! Actual local weak-word fields on the physical four-plus-three product
produce a smooth compatible representative on an interior seven-coordinate
box. The compact cutoff and mollifier are instantiated, all L2 limits are
proved, and the final pointwise constant uses the original local fields. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem product_local_weak_words7_quantitative_representative
    {Ω O : Set (Space (Fin 3))} (hΩ : IsOpen Ω) (hO : IsOpen O)
    {χ : Space (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hcχ : HasCompactSupport χ) (hsχ : tsupport χ ⊆ Ω)
    (hpχ : ∀ p ∈ O, χ p = 1)
    {a b : Fin 7 → ℝ} (hab : ∀ i, a i < b i)
    (hKO : MapsTo sevenToProduct (tensorClosedBox7 a b) O)
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U) (hUK : U ⊆ tensorClosedBox7 a b)
    (D : List (Fin 4 ⊕ Fin 3) → Space (Fin 3) → ℂ)
    (hL2 : ∀ w, ProductLocallyL2On (D w) Ω)
    (hD : ∀ w i, ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i))
    (M : List (Fin 7) → ℝ) (hM : ∀ w, 0 ≤ M w)
    (hDM : ∀ w s, Real.sqrt (∫ x in tensorClosedBox7 a b,
      ‖D ((canonicalSubsetWord7 s ++ w).map sevenCoordinateEquiv) (sevenToProduct x)‖^2) ≤ M w) :
    ∃ g : (Fin 7 → ℝ) → ℂ,
      ContinuousOn g (tensorClosedBox7 a b) ∧ ContDiffOn ℝ ∞ g U ∧
      (D [] ∘ sevenToProduct) =ᵐ[volume.restrict (tensorClosedBox7 a b)] g ∧
      (∀ w, (D (w.map sevenCoordinateEquiv) ∘ sevenToProduct)
        =ᵐ[volume.restrict U] coordinateWordDeriv7 g w) ∧
      (∀ w x, x ∈ U → ‖coordinateWordDeriv7 g w x‖ ≤ boxEvaluationConstant a b * M w) := by
  obtain ⟨F,hF,hFd⟩ := product_compact_cutoff_all_weak_word_family hΩ
    productCoordinateDirection hχ hcχ hsχ D hL2 hD
  let K := tensorClosedBox7 a b
  have hW (w : List (Fin 7)) :
      (productSevenWordLimit K F w : (Fin 7 → ℝ) → ℂ) =ᵐ[volume.restrict K]
        D (w.map sevenCoordinateEquiv) ∘ sevenToProduct := by
    have ha := sevenToProduct_measurePreserving.quasiMeasurePreserving.ae
      (hF (w.map sevenCoordinateEquiv))
    refine (productSevenWordLimit_ae K F w).trans ?_
    filter_upwards [ae_restrict_of_ae ha,ae_restrict_mem (tensorClosedBox7_isClosed a b).measurableSet]
      with x hx hxK
    exact hx.trans (directionalWordProduct_plateau productCoordinateDirection hO hpχ D _ (hKO hxK))
  have hWM (w : List (Fin 7)) (s : Finset (Fin 7)) :
      ‖productSevenWordLimit K F (canonicalSubsetWord7 s ++ w)‖ ≤ M w := by
    rw [← tensor_box_sqrt_integral_eq_Lp_norm _ (hW (canonicalSubsetWord7 s ++ w))]
    exact hDM w s
  obtain ⟨g,hgc,hgs,hg0,hgw,hgb⟩ := smooth_words7_quantitative_representative_of_L2_limits
    hab hU hUK (productSevenMollifier F) (productSevenMollifier_contDiff F)
    (productSevenMollifiedWordLp K F)
    (fun n w => productSevenMollifiedWordLp_ae K F (m := w.length)
      (fun v i _ => hFd v i) n w le_rfl)
    (productSevenWordLimit K F) (productSevenMollifiedWordLp_tendsto K F) M hM hWM
  refine ⟨g,hgc,hgs,?_,?_,hgb⟩
  · exact (hW []).symm.trans hg0
  · intro w
    exact ((hW w).filter_mono (ae_mono (Measure.restrict_mono_set volume hUK))).symm.trans (hgw w)

end TheoremT.Continuum
