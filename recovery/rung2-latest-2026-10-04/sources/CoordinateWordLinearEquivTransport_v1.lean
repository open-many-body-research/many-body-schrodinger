import ProductSevenCoordinateTransport_v1
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import SmoothComplexMixedSourceWords_v1

/-! Exact word derivatives under a continuous linear equivalence. Invertibility
makes the totalized fderiv chain rule valid without differentiability inputs;
this transports the recovered local representative to physical product space. -/
noncomputable section
set_option autoImplicit false
open Set MeasureTheory
namespace TheoremT.Continuum
open WeakGrushin

theorem normed_word_linearEquiv_transport
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {ι κ : Type*} (L : E ≃L[ℝ] F) (dE : ι → E) (dF : κ → F)
    (e : ι → κ) (he : ∀ i, L (dE i) = dF (e i)) (f : F → ℂ)
    (w : List ι) :
    normedComplexDirectionalWordDeriv dE (f ∘ L) w =
      normedComplexDirectionalWordDeriv dF f (w.map e) ∘ L := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (fun x => fderiv ℝ (normedComplexDirectionalWordDeriv dE (f ∘ L) w) x (dE i)) = _
    rw [ih]
    funext x
    rw [L.comp_right_fderiv]
    change fderiv ℝ (normedComplexDirectionalWordDeriv dF f (w.map e)) (L x) (L (dE i)) = _
    rw [he i]
    rfl

theorem normed_word_eq_product_word
    {κ : Type} [Fintype κ] [DecidableEq κ]
    {ι : Type} (dirs : ι → Space κ) (f : Space κ → ℂ) (w : List ι) :
    normedComplexDirectionalWordDeriv dirs f w = WeakGrushin.complexDirectionalWordDeriv dirs f w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    simp only [normedComplexDirectionalWordDeriv, WeakGrushin.complexDirectionalWordDeriv, ih]

theorem sevenToProduct_all_word_chain (f : Space (Fin 3) → ℂ) (w : List (Fin 7)) :
    coordinateWordDeriv7 (f ∘ sevenToProduct) w =
      WeakGrushin.complexDirectionalWordDeriv productCoordinateDirection f
        (w.map sevenCoordinateEquiv) ∘ sevenToProduct := by
  exact (normed_word_linearEquiv_transport sevenToProduct (fun i => Pi.single i 1)
    productCoordinateDirection sevenCoordinateEquiv sevenToProduct_direction f w).trans
    (congrArg (fun f => f ∘ sevenToProduct) (normed_word_eq_product_word _ f _))

theorem sevenToProduct_symm_direction (i : Fin 4 ⊕ Fin 3) :
    sevenToProduct.symm (productCoordinateDirection i) = Pi.single (sevenCoordinateEquiv.symm i) (1 : ℝ) := by
  apply sevenToProduct.injective
  rw [sevenToProduct.apply_symm_apply, sevenToProduct_direction, sevenCoordinateEquiv.apply_symm_apply]

theorem sevenToProduct_symm_all_word_chain (g : (Fin 7 → ℝ) → ℂ)
    (w : List (Fin 4 ⊕ Fin 3)) :
    WeakGrushin.complexDirectionalWordDeriv productCoordinateDirection (g ∘ sevenToProduct.symm) w =
      coordinateWordDeriv7 g (w.map sevenCoordinateEquiv.symm) ∘ sevenToProduct.symm := by
  rw [← normed_word_eq_product_word]
  exact normed_word_linearEquiv_transport sevenToProduct.symm productCoordinateDirection
    (fun i => Pi.single i 1) sevenCoordinateEquiv.symm sevenToProduct_symm_direction g w

end TheoremT.Continuum
