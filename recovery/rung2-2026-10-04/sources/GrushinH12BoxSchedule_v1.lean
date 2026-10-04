import GrushinRectangularBoxGeometry_v1

/-! The exact geometric shrinking schedule for twelve tangential gains and
five Y-elliptic gains. Indices are real, allowing intermediate collars.
These results establish only box geometry, not an analytic H12 conclusion. -/
noncomputable section
open scoped Topology
namespace TheoremT.Continuum.WeakGrushin

def h12BoxGap (aY aT bY bT : ℝ) : ℝ := min (aY-bY) (aT-bT) / 34

def h12BoxRadius (a δ j : ℝ) : ℝ := a-j*δ

def h12ScheduledBox (center : Space (Fin 3)) (aY aT δ j : ℝ) :
    Set (Space (Fin 3)) :=
  rectangularOpenBox center (h12BoxRadius aY δ j) (h12BoxRadius aT δ j)

theorem h12BoxGap_pos {aY aT bY bT : ℝ} (hy : bY < aY) (ht : bT < aT) :
    0 < h12BoxGap aY aT bY bT :=
  div_pos (lt_min (sub_pos.mpr hy) (sub_pos.mpr ht)) (by norm_num)

theorem h12BoxGap_y_margin (aY aT bY bT : ℝ) :
    34*h12BoxGap aY aT bY bT ≤ aY-bY := by
  have he : 34*h12BoxGap aY aT bY bT = min (aY-bY) (aT-bT) := by
    unfold h12BoxGap
    ring
  rw [he]
  exact min_le_left _ _

theorem h12BoxGap_t_margin (aY aT bY bT : ℝ) :
    34*h12BoxGap aY aT bY bT ≤ aT-bT := by
  have he : 34*h12BoxGap aY aT bY bT = min (aY-bY) (aT-bT) := by
    unfold h12BoxGap
    ring
  rw [he]
  exact min_le_right _ _

theorem h12ScheduledBox_isOpen (center : Space (Fin 3)) (aY aT δ j : ℝ) :
    IsOpen (h12ScheduledBox center aY aT δ j) :=
  rectangularOpenBox_isOpen center _ _

theorem h12_target_subset_level34 (center : Space (Fin 3)) (aY aT bY bT : ℝ) :
    rectangularOpenBox center bY bT ⊆
      h12ScheduledBox center aY aT (h12BoxGap aY aT bY bT) 34 := by
  have hy : bY ≤ h12BoxRadius aY (h12BoxGap aY aT bY bT) 34 := by
    unfold h12BoxRadius
    linarith [h12BoxGap_y_margin aY aT bY bT]
  have ht : bT ≤ h12BoxRadius aT (h12BoxGap aY aT bY bT) 34 := by
    unfold h12BoxRadius
    linarith [h12BoxGap_t_margin aY aT bY bT]
  intro p hp i
  cases i with
  | inl i => exact (hp (.inl i)).trans_le hy
  | inr i => exact (hp (.inr i)).trans_le ht

theorem h12BoxRadius_two_gap_y {aY aT bY bT j : ℝ}
    (hby : 0 < bY) (hy : bY < aY) (ht : bT < aT) (hj : j ≤ 32) :
    2*h12BoxGap aY aT bY bT ≤ h12BoxRadius aY (h12BoxGap aY aT bY bT) j := by
  have hδ := (h12BoxGap_pos hy ht).le
  have hjδ := mul_le_mul_of_nonneg_right hj hδ
  have hm := h12BoxGap_y_margin aY aT bY bT
  unfold h12BoxRadius
  linarith

theorem h12BoxRadius_two_gap_t {aY aT bY bT j : ℝ}
    (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT) (hj : j ≤ 32) :
    2*h12BoxGap aY aT bY bT ≤ h12BoxRadius aT (h12BoxGap aY aT bY bT) j := by
  have hδ := (h12BoxGap_pos hy ht).le
  have hjδ := mul_le_mul_of_nonneg_right hj hδ
  have hm := h12BoxGap_t_margin aY aT bY bT
  unfold h12BoxRadius
  linarith

theorem h12ScheduledBox_y_radius (center : Space (Fin 3)) {aY aT δ j : ℝ}
    (hδ : 0 ≤ δ) (hj : 0 ≤ j) {p : Space (Fin 3)}
    (hp : p ∈ h12ScheduledBox center aY aT δ j) :
    ‖p.1‖ ≤ ‖center.1‖+2*aY := by
  have hr : 0 ≤ h12BoxRadius aY δ j :=
    (lt_of_le_of_lt (abs_nonneg _) (hp (.inl 0))).le
  have hc : p ∈ rectangularClosedBox center (h12BoxRadius aY δ j)
      (h12BoxRadius aT δ j) :=
    rectangularOpenBox_subset_closedBox center _ _ hp
  have hb := rectangularClosedBox_y_radius center hr hc
  have hmul := mul_nonneg hj hδ
  unfold h12BoxRadius at hb
  linarith

#print axioms h12_target_subset_level34
#print axioms h12BoxRadius_two_gap_y
#print axioms h12BoxRadius_two_gap_t
#print axioms h12ScheduledBox_y_radius

end TheoremT.Continuum.WeakGrushin
