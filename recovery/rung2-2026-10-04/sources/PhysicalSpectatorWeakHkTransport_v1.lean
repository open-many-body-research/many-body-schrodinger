import PhysicalSpectatorL2BudgetTransport_v1
import PhysicalSpectatorWeakEquationTransport_v1
import PhysicalSpectatorFactorialWords_v1
import ProductMixedMultiIndexWeakHk_v1

/-! Transport of genuine local weak coordinate jets from either two-electron
physical spectator space to the canonical four-plus-three coordinate space.
The weak identities use smooth test pullback and product-volume change of
variables. Every word and every squared L2 budget retains its exact order
and value. The final H12 result is a specialization of the finite-order
theorem, with no higher regularity premise. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum
open WeakGrushin

theorem physicalSpectatorReindexAt_localWeakDirectional (i : Fin 2)
    {Ω : Set (Space (Fin 3))} {f d : NuclearKSSpace i → ℂ} {v : Space (Fin 3)}
    (hd : ProductLocalWeakDirectional (physicalSpectatorReindexAt i ⁻¹' Ω)
      f d ((physicalSpectatorReindexAt i).symm v)) :
    ProductLocalWeakDirectional Ω (f ∘ (physicalSpectatorReindexAt i).symm)
      (d ∘ (physicalSpectatorReindexAt i).symm) v := by
  refine ⟨physicalSpectatorReindexAt_locallyL2 i hd.1,
    physicalSpectatorReindexAt_locallyL2 i hd.2.1, ?_⟩
  intro φ hφ hc hs
  obtain ⟨hφR, hcR, htR⟩ := physicalSpectatorReindexAt_cutoff_test i hφ hc
  have hsR : tsupport (φ ∘ physicalSpectatorReindexAt i) ⊆
      physicalSpectatorReindexAt i ⁻¹' Ω := by
    rw [htR]
    exact Set.preimage_mono hs
  have he := hd.2.2 (φ ∘ physicalSpectatorReindexAt i) hφR hcR hsR
  let L : Space (Fin 3) → ℂ := fun p => φ p • d ((physicalSpectatorReindexAt i).symm p)
  let R : Space (Fin 3) → ℂ := fun p =>
    fderiv ℝ φ p v • f ((physicalSpectatorReindexAt i).symm p)
  have hLc : L ∘ physicalSpectatorReindexAt i =
      fun p => (φ ∘ physicalSpectatorReindexAt i) p • d p := by
    ext p
    simp only [L, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply]
  have hRc : R ∘ physicalSpectatorReindexAt i = fun p =>
      fderiv ℝ (φ ∘ physicalSpectatorReindexAt i) p
        ((physicalSpectatorReindexAt i).symm v) • f p := by
    ext p
    simp only [R, Function.comp_apply, LinearIsometryEquiv.symm_apply_apply,
      physicalSpectatorReindexAt_cutoff_first i hφ, LinearIsometryEquiv.apply_symm_apply]
  have hp := physicalSpectatorReindexAt_measurePreserving i
  have hm := (physicalSpectatorReindexAt i).toHomeomorph.measurableEmbedding
  change (∫ p, L p) = -(∫ p, R p)
  rw [← hp.integral_comp hm L, ← hp.integral_comp hm R]
  change (∫ p, (L ∘ physicalSpectatorReindexAt i) p) =
    -(∫ p, (R ∘ physicalSpectatorReindexAt i) p)
  rw [hLc, hRc]
  exact he

theorem physicalSpectatorReindexAt_coordinateWeakHk (i : Fin 2)
    {Ω : Set (Space (Fin 3))} {f : NuclearKSSpace i → ℂ} {m : ℕ} {W : ℝ}
    (hf : ProductCoordinateWeakHk (physicalSpectatorReindexAt i ⁻¹' Ω) f m W) :
    ProductCoordinateWeakHk Ω (f ∘ (physicalSpectatorReindexAt i).symm) m W := by
  obtain ⟨D, h0, hBudget, hChain⟩ := hf
  let q : Fin 4 ⊕ Fin 3 → Fin 4 ⊕ SpectatorCoordinate i :=
    Sum.map id (twoElectronSpectatorCoordinateEquiv i).symm
  let D' := fun w : List (Fin 4 ⊕ Fin 3) =>
    D (w.map q) ∘ (physicalSpectatorReindexAt i).symm
  refine ⟨D', ?_, ?_, ?_⟩
  · change D [] ∘ (physicalSpectatorReindexAt i).symm = _
    rw [h0]
  · intro w hw
    exact physicalSpectatorReindexAt_regionL2Budget i (hBudget (w.map q) (by
      simpa only [List.length_map] using hw))
  · intro w j hw
    apply physicalSpectatorReindexAt_localWeakDirectional i
    change ProductLocalWeakDirectional (physicalSpectatorReindexAt i ⁻¹' Ω)
      (D (w.map q)) (D (q j :: w.map q))
      ((physicalSpectatorReindexAt i).symm (productCoordinateDirection j))
    rw [physicalSpectatorReindexAt_symm_coordinate]
    exact hChain (w.map q) (q j) (by simpa only [List.length_map] using hw)

theorem physicalSpectatorReindexAt_mixedMultiIndexWeakHk (i : Fin 2)
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {f : NuclearKSSpace i → ℂ} {m : ℕ} {W : ℝ}
    (hf : ProductCoordinateWeakHk (physicalSpectatorReindexAt i ⁻¹' Ω) f m W) :
    ProductMixedMultiIndexWeakHk Ω (f ∘ (physicalSpectatorReindexAt i).symm) m W :=
  coordinateWeakHk_mixed_multiIndex hΩ (physicalSpectatorReindexAt_coordinateWeakHk i hf)

theorem physicalSpectatorReindexAt_mixedH12 (i : Fin 2)
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    {f : NuclearKSSpace i → ℂ} {W : ℝ}
    (hf : ProductCoordinateWeakHk (physicalSpectatorReindexAt i ⁻¹' Ω) f 12 W) :
    ProductMixedMultiIndexWeakHk Ω (f ∘ (physicalSpectatorReindexAt i).symm) 12 W :=
  physicalSpectatorReindexAt_mixedMultiIndexWeakHk i hΩ hf

end TheoremT.Continuum
