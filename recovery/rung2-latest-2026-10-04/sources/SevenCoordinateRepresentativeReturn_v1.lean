import CoordinateWordLinearEquivTransport_v1

/-! A recovered seven-coordinate representative is returned to the actual
physical product with its ordinary product norm and Lebesgue measure. Actual
word derivatives and all pointwise bounds are preserved exactly. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem sevenToProduct_symm_measurePreserving :
    MeasurePreserving sevenToProduct.symm volume volume :=
  MeasurePreserving.symm sevenToProduct.toHomeomorph.toMeasurableEquiv sevenToProduct_measurePreserving

theorem sevenToProduct_ae_return
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U)
    {f : Space (Fin 3) → ℂ} {g : (Fin 7 → ℝ) → ℂ}
    (hfg : (f ∘ sevenToProduct) =ᵐ[volume.restrict U] g) :
    f =ᵐ[volume.restrict (Set.image sevenToProduct U)] (g ∘ sevenToProduct.symm) := by
  have hp := sevenToProduct_symm_measurePreserving.quasiMeasurePreserving.ae (ae_imp_of_ae_restrict hfg)
  have hopen : IsOpen (Set.image sevenToProduct U) := sevenToProduct.toHomeomorph.isOpenMap U hU
  filter_upwards [ae_restrict_of_ae hp,ae_restrict_mem hopen.measurableSet] with p hp hpU
  obtain ⟨x,hx,rfl⟩ := hpU
  simpa only [Function.comp_apply,ContinuousLinearEquiv.symm_apply_apply] using hp (by simpa using hx)

theorem seven_coordinate_smooth_representative_return
    {U : Set (Fin 7 → ℝ)} (hU : IsOpen U)
    (D : List (Fin 4 ⊕ Fin 3) → Space (Fin 3) → ℂ)
    (g : (Fin 7 → ℝ) → ℂ) (hg : ContDiffOn ℝ ∞ g U)
    (hDg : ∀ w, (D (w.map sevenCoordinateEquiv) ∘ sevenToProduct)
      =ᵐ[volume.restrict U] coordinateWordDeriv7 g w)
    (B : List (Fin 7) → ℝ)
    (hBg : ∀ w x, x ∈ U → ‖coordinateWordDeriv7 g w x‖ ≤ B w) :
    ContDiffOn ℝ ∞ (g ∘ sevenToProduct.symm) (Set.image sevenToProduct U) ∧
      (∀ w, D w =ᵐ[volume.restrict (Set.image sevenToProduct U)]
        complexDirectionalWordDeriv productCoordinateDirection (g ∘ sevenToProduct.symm) w) ∧
      (∀ w p, p ∈ Set.image sevenToProduct U →
        ‖complexDirectionalWordDeriv productCoordinateDirection (g ∘ sevenToProduct.symm) w p‖ ≤
          B (w.map sevenCoordinateEquiv.symm)) := by
  have hmap : MapsTo sevenToProduct.symm (Set.image sevenToProduct U) U := by
    rintro p ⟨x,hx,rfl⟩
    simpa using hx
  refine ⟨hg.comp sevenToProduct.symm.contDiff.contDiffOn hmap, ?_, ?_⟩
  · intro w
    have ha := sevenToProduct_ae_return hU (hDg (w.map sevenCoordinateEquiv.symm))
    rw [sevenToProduct_symm_all_word_chain]
    simpa [List.map_map,Function.comp_def] using ha
  · intro w p hp
    rw [sevenToProduct_symm_all_word_chain]
    exact hBg (w.map sevenCoordinateEquiv.symm) (sevenToProduct.symm p) (hmap hp)

end TheoremT.Continuum
