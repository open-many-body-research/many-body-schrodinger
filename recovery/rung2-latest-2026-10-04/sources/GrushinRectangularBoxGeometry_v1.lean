import GrushinCoordinateBoxGeometry_v1

/-! Rectangular boxes with separate four-dimensional Y and three-dimensional
T half-widths in the actual Grushin product space. The Y coefficient radius
retains its own half-width rather than the maximum of both widths. -/
noncomputable section
open scoped Topology BigOperators
namespace TheoremT.Continuum.WeakGrushin

def boxHalfWidth (ry rt : ℝ) : Fin 4 ⊕ Fin 3 → ℝ
  | .inl _ => ry
  | .inr _ => rt

def rectangularClosedBox (a : Space (Fin 3)) (ry rt : ℝ) : Set (Space (Fin 3)) :=
  {p | ∀ i, |boxCoordinate i (p-a)| ≤ boxHalfWidth ry rt i}

def rectangularOpenBox (a : Space (Fin 3)) (ry rt : ℝ) : Set (Space (Fin 3)) :=
  {p | ∀ i, |boxCoordinate i (p-a)| < boxHalfWidth ry rt i}

theorem rectangularClosedBox_isClosed (a : Space (Fin 3)) (ry rt : ℝ) :
    IsClosed (rectangularClosedBox a ry rt) := by
  have he : rectangularClosedBox a ry rt =
      ⋂ i, {p | |boxCoordinate i (p-a)| ≤ boxHalfWidth ry rt i} := by
    ext p
    simp [rectangularClosedBox]
  rw [he]
  apply isClosed_iInter
  intro i
  exact isClosed_le (((boxCoordinate i).continuous.comp
    (continuous_id.sub continuous_const)).abs) continuous_const

theorem rectangularOpenBox_isOpen (a : Space (Fin 3)) (ry rt : ℝ) :
    IsOpen (rectangularOpenBox a ry rt) := by
  have he : rectangularOpenBox a ry rt =
      ⋂ i, {p | |boxCoordinate i (p-a)| < boxHalfWidth ry rt i} := by
    ext p
    simp [rectangularOpenBox]
  rw [he]
  apply isOpen_iInter_of_finite
  intro i
  exact isOpen_lt (((boxCoordinate i).continuous.comp
    (continuous_id.sub continuous_const)).abs) continuous_const

theorem rectangularClosedBox_subset_coordinateClosedBox
    (a : Space (Fin 3)) (ry rt : ℝ) :
    rectangularClosedBox a ry rt ⊆ coordinateClosedBox a (max ry rt) := by
  intro p hp i
  cases i with
  | inl i => exact (hp (.inl i)).trans (le_max_left _ _)
  | inr j => exact (hp (.inr j)).trans (le_max_right _ _)

theorem rectangularClosedBox_isCompact (a : Space (Fin 3)) {ry rt : ℝ}
    (hry : 0 ≤ ry) (hrt : 0 ≤ rt) :
    IsCompact (rectangularClosedBox a ry rt) :=
  (coordinateClosedBox_isCompact a (le_max_of_le_left hry)).of_isClosed_subset
    (rectangularClosedBox_isClosed a ry rt)
    (rectangularClosedBox_subset_coordinateClosedBox a ry rt)

theorem rectangularClosedBox_y_norm (a : Space (Fin 3)) {ry rt : ℝ}
    (hry : 0 ≤ ry) {p : Space (Fin 3)}
    (hp : p ∈ rectangularClosedBox a ry rt) : ‖p.1-a.1‖ ≤ 2*ry := by
  have hsq : ‖p.1-a.1‖^2 ≤ 4*ry^2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin 4, ry^2 := Finset.sum_le_sum (fun i _ => by
        have hi : |p.1 i-a.1 i| ≤ ry := hp (.inl i)
        simpa only [sq_abs, PiLp.sub_apply] using pow_le_pow_left₀ (abs_nonneg _) hi 2)
      _ = _ := by simp
  nlinarith [norm_nonneg (p.1-a.1)]

theorem rectangularClosedBox_y_radius (a : Space (Fin 3)) {ry rt : ℝ}
    (hry : 0 ≤ ry) {p : Space (Fin 3)}
    (hp : p ∈ rectangularClosedBox a ry rt) : ‖p.1‖ ≤ ‖a.1‖+2*ry := by
  calc
    ‖p.1‖ = ‖(p.1-a.1)+a.1‖ := by rw [sub_add_cancel]
    _ ≤ ‖p.1-a.1‖+‖a.1‖ := norm_add_le _ _
    _ ≤ 2*ry+‖a.1‖ := add_le_add (rectangularClosedBox_y_norm a hry hp) (le_refl _)
    _ = _ := by ring

theorem rectangularClosedBox_subset_openBox (a : Space (Fin 3))
    {ry rt Ry Rt : ℝ} (hy : ry < Ry) (ht : rt < Rt) :
    rectangularClosedBox a ry rt ⊆ rectangularOpenBox a Ry Rt := by
  intro p hp i
  cases i with
  | inl i => exact (hp (.inl i)).trans_lt hy
  | inr j => exact (hp (.inr j)).trans_lt ht

theorem rectangularOpenBox_subset_closedBox (a : Space (Fin 3)) (ry rt : ℝ) :
    rectangularOpenBox a ry rt ⊆ rectangularClosedBox a ry rt :=
  fun _ hp i => (hp i).le

#print axioms rectangularClosedBox_isCompact
#print axioms rectangularClosedBox_y_radius
#print axioms rectangularClosedBox_subset_openBox

end TheoremT.Continuum.WeakGrushin
