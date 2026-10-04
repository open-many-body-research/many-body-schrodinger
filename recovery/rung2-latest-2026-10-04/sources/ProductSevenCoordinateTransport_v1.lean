import ProductWeakWordMollification_v1
import ProductCoordinateWeakHk_v1
import CoordinateMultiIndexWord_v1
import SmoothCoordinateSubsetFields7_v1
import Mathlib.MeasureTheory.Constructions.Pi

/-! Literal seven-coordinate transport to the physical four-plus-three product.
Both the derivative directions and the Lebesgue measure are identified exactly. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
open WeakGrushin

def sevenToProduct : (Fin 7 → ℝ) ≃L[ℝ] Space (Fin 3) :=
  (ContinuousLinearEquiv.piCongrLeft ℝ (fun _ : Fin 4 ⊕ Fin 3 => ℝ) sevenCoordinateEquiv).trans
    ((ContinuousLinearEquiv.sumPiEquivProdPi ℝ (Fin 4) (Fin 3) (fun _ => ℝ)).trans
      ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 4 => ℝ)).symm.prodCongr
       (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).symm))

theorem sevenToProduct_measurePreserving : MeasurePreserving sevenToProduct volume volume := by
  exact ((PiLp.volume_preserving_toLp (Fin 4)).prod
    (PiLp.volume_preserving_toLp (Fin 3))).comp
    ((volume_measurePreserving_sumPiEquivProdPi (fun _ : Fin 4 ⊕ Fin 3 => ℝ)).comp
      (volume_measurePreserving_piCongrLeft (fun _ : Fin 4 ⊕ Fin 3 => ℝ) sevenCoordinateEquiv))

theorem sevenToProduct_direction (i : Fin 7) :
    sevenToProduct (Pi.single i (1 : ℝ)) = productCoordinateDirection (sevenCoordinateEquiv i) := by
  apply Prod.ext
  · ext j
    simp only [sevenToProduct,ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.prodCongr_apply,PiLp.coe_symm_continuousLinearEquiv,WithLp.ofLp_toLp,ContinuousLinearEquiv.sumPiEquivProdPi,ContinuousLinearEquiv.piCongrLeft,LinearEquiv.sumPiEquivProdPi,Homeomorph.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft',Equiv.sumPiEquivProdPi]
    change (Equiv.piCongrLeft (fun _ : Fin 4 ⊕ Fin 3 => ℝ) sevenCoordinateEquiv (Pi.single i (1 : ℝ))) (Sum.inl j) = _
    simp only [Equiv.piCongrLeft_apply,eq_rec_constant]
    cases h : sevenCoordinateEquiv i with
    | inl k =>
      have hi : i = sevenCoordinateEquiv.symm (Sum.inl k) := by rw [← h]; simp
      subst i
      simp [productCoordinateDirection,yDir,EuclideanSpace.basisFun_apply,Pi.single_apply,← Equiv.apply_eq_iff_eq_symm_apply]
    | inr k =>
      have hi : i = sevenCoordinateEquiv.symm (Sum.inr k) := by rw [← h]; simp
      subst i
      simp [productCoordinateDirection,tDir,Pi.single_apply]
  · ext j
    simp only [sevenToProduct,ContinuousLinearEquiv.trans_apply,ContinuousLinearEquiv.prodCongr_apply,PiLp.coe_symm_continuousLinearEquiv,WithLp.ofLp_toLp,ContinuousLinearEquiv.sumPiEquivProdPi,ContinuousLinearEquiv.piCongrLeft,LinearEquiv.sumPiEquivProdPi,Homeomorph.piCongrLeft,Equiv.piCongrLeft,Equiv.piCongrLeft',Equiv.sumPiEquivProdPi]
    change (Equiv.piCongrLeft (fun _ : Fin 4 ⊕ Fin 3 => ℝ) sevenCoordinateEquiv (Pi.single i (1 : ℝ))) (Sum.inr j) = _
    simp only [Equiv.piCongrLeft_apply,eq_rec_constant]
    cases h : sevenCoordinateEquiv i with
    | inl k =>
      have hi : i = sevenCoordinateEquiv.symm (Sum.inl k) := by rw [← h]; simp
      subst i
      simp [productCoordinateDirection,yDir,Pi.single_apply]
    | inr k =>
      have hi : i = sevenCoordinateEquiv.symm (Sum.inr k) := by rw [← h]; simp
      subst i
      simp [productCoordinateDirection,tDir,EuclideanSpace.basisFun_apply,Pi.single_apply,← Equiv.apply_eq_iff_eq_symm_apply]

theorem sevenToProduct_word_chain
    (D : List (Fin 4 ⊕ Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3))))
    (n : ℕ) (w : List (Fin 7)) :
    coordinateWordDeriv7 (productMollifiedWord productCoordinateDirection D n [] ∘ sevenToProduct) w =
      productMollifiedWord productCoordinateDirection D n (w.map sevenCoordinateEquiv) ∘ sevenToProduct := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change (fun x => fderiv ℝ (coordinateWordDeriv7 _ w) x (Pi.single i (1 : ℝ))) = _
    rw [ih]
    funext x
    have hh := ((productMollifiedWord_contDiff productCoordinateDirection D n
      (w.map sevenCoordinateEquiv)).differentiable (by simp)).differentiableAt.hasFDerivAt.comp x sevenToProduct.hasFDerivAt
    rw [hh.fderiv]
    change fderiv ℝ (productMollifiedWord productCoordinateDirection D n (w.map sevenCoordinateEquiv))
      (sevenToProduct x) (sevenToProduct (Pi.single i (1 : ℝ))) = _
    rw [sevenToProduct_direction,productMollifiedWord_directional]
    rfl

end TheoremT.Continuum
