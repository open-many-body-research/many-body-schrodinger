import GrushinQuadraticYWordBound_v1
import ProductCoordinateWeakHk_v1

/-! Exact derivatives of the quadratic Grushin weight in every product
coordinate, including spectator directions. Only one and two equal Y
letters contribute to a nonempty coefficient word. -/
noncomputable section
open scoped ContDiff RealInnerProductSpace BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem grushin_quadratic_coordinate_word_singleton
    (x : Fin 4 ⊕ κ) (p : Space κ) :
    directionalWordDeriv productCoordinateDirection (fun q : Space κ => ‖q.1‖^2) [x] p =
      2 * inner ℝ (productCoordinateDirection x).1 p.1 := by
  have hn : ContDiff ℝ ∞ (fun y : KSSpace => ‖y‖^2) := contDiff_norm_sq ℝ
  change fderiv ℝ (fun q : Space κ => ‖q.1‖^2) p (productCoordinateDirection x) = _
  rw [first_directional_fst (hn.differentiable (by simp)), fderiv_norm_sq_apply]
  rw [real_inner_comm]
  simp

theorem grushin_quadratic_coordinate_word_pair
    (x z : Fin 4 ⊕ κ) (p : Space κ) :
    directionalWordDeriv productCoordinateDirection (fun q : Space κ => ‖q.1‖^2) [x,z] p =
      2 * inner ℝ (productCoordinateDirection z).1 (productCoordinateDirection x).1 := by
  have hfirst : directionalWordDeriv productCoordinateDirection
      (fun q : Space κ => ‖q.1‖^2) [z] =
      (fun q : Space κ => ((2 : ℝ) • innerSL ℝ (productCoordinateDirection z).1) q.1) := by
    funext q
    rw [grushin_quadratic_coordinate_word_singleton]
    simp
  change fderiv ℝ (directionalWordDeriv productCoordinateDirection
    (fun q : Space κ => ‖q.1‖^2) [z]) p (productCoordinateDirection x) = _
  rw [hfirst, first_directional_fst
    (((2 : ℝ) • innerSL ℝ (productCoordinateDirection z).1).differentiable),
    ContinuousLinearMap.fderiv]
  simp

theorem grushin_quadratic_coordinate_word_triple
    (x z u : Fin 4 ⊕ κ) (p : Space κ) :
    directionalWordDeriv productCoordinateDirection (fun q : Space κ => ‖q.1‖^2) [x,z,u] p = 0 := by
  have hsecond : directionalWordDeriv productCoordinateDirection
      (fun q : Space κ => ‖q.1‖^2) [z,u] =
      (fun _ : Space κ => 2 * inner ℝ (productCoordinateDirection u).1
        (productCoordinateDirection z).1) :=
    funext (grushin_quadratic_coordinate_word_pair z u)
  change fderiv ℝ (directionalWordDeriv productCoordinateDirection
    (fun q : Space κ => ‖q.1‖^2) [z,u]) p (productCoordinateDirection x) = 0
  rw [hsecond]
  simp

theorem grushin_quadratic_coordinate_word_vanishes
    (w : List (Fin 4 ⊕ κ)) (hw : 3 ≤ w.length) (p : Space κ) :
    directionalWordDeriv productCoordinateDirection (fun q : Space κ => ‖q.1‖^2) w p = 0 := by
  induction w generalizing p with
  | nil => simp at hw
  | cons x w ih =>
    by_cases ht : 3 ≤ w.length
    · have hz : directionalWordDeriv productCoordinateDirection
          (fun q : Space κ => ‖q.1‖^2) w = (fun _ => 0) := funext (ih ht)
      change fderiv ℝ (directionalWordDeriv productCoordinateDirection
        (fun q : Space κ => ‖q.1‖^2) w) p (productCoordinateDirection x) = 0
      rw [hz]
      simp
    · have hl : w.length = 2 := by simp only [List.length_cons] at hw; omega
      obtain ⟨z,u,rfl⟩ := List.length_eq_two.mp hl
      exact grushin_quadratic_coordinate_word_triple x z u p

theorem grushin_quadratic_coordinate_word_singleton_y
    (i : Fin 4) (p : Space κ) :
    directionalWordDeriv productCoordinateDirection
      (fun q : Space κ => ‖q.1‖^2) [Sum.inl i] p = 2 * p.1 i := by
  rw [grushin_quadratic_coordinate_word_singleton]
  simp [productCoordinateDirection, yDir, oscillatorBasis, EuclideanSpace.inner_single_left]

theorem grushin_quadratic_coordinate_word_pair_y
    (i k : Fin 4) (p : Space κ) :
    directionalWordDeriv productCoordinateDirection
      (fun q : Space κ => ‖q.1‖^2) [Sum.inl i,Sum.inl k] p = if i = k then 2 else 0 := by
  rw [grushin_quadratic_coordinate_word_pair]
  by_cases hik : i = k <;>
    simp [productCoordinateDirection, yDir, oscillatorBasis,
      EuclideanSpace.inner_single_left, hik, Ne.symm]

theorem grushin_quadratic_coordinate_word_nonempty
    (w : List (Fin 4 ⊕ κ)) (hw : w ≠ []) (p : Space κ) :
    directionalWordDeriv productCoordinateDirection (fun q : Space κ => ‖q.1‖^2) w p =
      (∑ i : Fin 4, if w = [Sum.inl i] then 2 * p.1 i else 0) +
      ∑ i : Fin 4, if w = [Sum.inl i,Sum.inl i] then 2 else 0 := by
  rcases w with _ | ⟨x,w⟩
  · exact (hw rfl).elim
  rcases w with _ | ⟨z,w⟩
  · cases x with
    | inl i => simp [grushin_quadratic_coordinate_word_singleton_y]
    | inr j => simp [grushin_quadratic_coordinate_word_singleton,
        productCoordinateDirection, tDir]
  rcases w with _ | ⟨u,w⟩
  · cases x with
    | inl i =>
      cases z with
      | inl k =>
        by_cases hik : i = k
        · subst k
          simp [grushin_quadratic_coordinate_word_pair_y]
        · have hnot (l : Fin 4) : ¬(i = l ∧ k = l) := by
            rintro ⟨hi,hk⟩
            exact hik (hi.trans hk.symm)
          simp [grushin_quadratic_coordinate_word_pair_y, hik, hnot]
      | inr j => simp [grushin_quadratic_coordinate_word_pair,
          productCoordinateDirection, yDir, tDir]
    | inr j => simp [grushin_quadratic_coordinate_word_pair,
        productCoordinateDirection, tDir]
  · rw [grushin_quadratic_coordinate_word_vanishes (x :: z :: u :: w) (by simp)]
    simp

end TheoremT.Continuum.WeakGrushin
