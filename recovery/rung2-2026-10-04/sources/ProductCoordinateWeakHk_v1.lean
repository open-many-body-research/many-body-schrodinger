import MixedTriangularState_v1

/-! Genuine finite Sobolev coordinate jets on the product region. An
arbitrary interleaved coordinate word is represented by its ordered Y and T
subwords. The existing mixed weak chains prove every next coordinate
identity. No smoothness, commutation, or higher weak derivative is assumed.
-/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def coordinateYWord : List (Fin 4 ⊕ κ) → List (Fin 4)
  | [] => []
  | Sum.inl i :: w => i :: coordinateYWord w
  | Sum.inr _ :: w => coordinateYWord w

def coordinateTWord : List (Fin 4 ⊕ κ) → List κ
  | [] => []
  | Sum.inl _ :: w => coordinateTWord w
  | Sum.inr j :: w => j :: coordinateTWord w

def productCoordinateDirection : Fin 4 ⊕ κ → Space κ
  | Sum.inl i => yDir i
  | Sum.inr j => tDir j

theorem coordinateWord_length (w : List (Fin 4 ⊕ κ)) :
    (coordinateYWord w).length+(coordinateTWord w).length = w.length := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    cases i <;> simp only [coordinateYWord,coordinateTWord,List.length_cons] <;> omega

def ProductCoordinateWeakHk (Ω : Set (Space κ)) (f : Space κ → ℂ)
    (m : ℕ) (W : ℝ) : Prop :=
  ∃ D : List (Fin 4 ⊕ κ) → Space κ → ℂ,
    D [] = f ∧
    (∀ w, w.length ≤ m → RegionL2Budget (D w) Ω W) ∧
    ∀ w i, w.length < m →
      ProductLocalWeakDirectional Ω (D w) (D (i :: w)) (productCoordinateDirection i)

theorem mixedTriangularState_coordinateWeakHk
    {Ω : Set (Space κ)} {f : Space κ → ℂ} {m : ℕ} {W : ℝ}
    (hf : MixedTriangularState Ω f m m W) : ProductCoordinateWeakHk Ω f m W := by
  obtain ⟨F,h0,hF,hY,hT⟩ := hf
  let D := fun w : List (Fin 4 ⊕ κ) => F (coordinateYWord w) (coordinateTWord w)
  refine ⟨D,h0,?_,?_⟩
  · intro w hw
    have hn := coordinateWord_length w
    exact hF _ _ (by omega) (by omega)
  · intro w i hw
    have hn := coordinateWord_length w
    cases i with
    | inl i => exact hY _ _ i (by omega) (by omega)
    | inr j => exact hT _ _ j (by omega) (by omega)

#print axioms coordinateWord_length
#print axioms mixedTriangularState_coordinateWeakHk
end TheoremT.Continuum.WeakGrushin
