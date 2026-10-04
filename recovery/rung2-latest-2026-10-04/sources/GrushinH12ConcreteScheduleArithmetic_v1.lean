import GrushinH12BoxSchedule_v1

/-! Exact rational arithmetic for the 34-gap rectangular schedule. All stage
indices are real, allowing both integer stages and intermediate collars.
These lemmas provide geometry only, with no regularity or physical-patch claim. -/
noncomputable section
open scoped Topology
namespace TheoremT.Continuum.WeakGrushin

def h12ConcreteDelta : ℝ := 1 / 4352

def h12ConcreteRadius (j : ℝ) : ℝ := h12BoxRadius (1 / 64) h12ConcreteDelta j

def h12ConcreteBox (center : Space (Fin 3)) (j : ℝ) : Set (Space (Fin 3)) :=
  h12ScheduledBox center (1 / 64) (1 / 64) h12ConcreteDelta j

theorem h12ConcreteDelta_pos : 0 < h12ConcreteDelta := by
  norm_num [h12ConcreteDelta]

theorem h12ConcreteDelta_eq_boxGap :
    h12ConcreteDelta = h12BoxGap (1 / 64) (1 / 64) (1 / 128) (1 / 128) := by
  norm_num [h12ConcreteDelta, h12BoxGap]

theorem h12ConcreteRadius_eq (j : ℝ) :
    h12ConcreteRadius j = 1 / 64 - j * h12ConcreteDelta := rfl

theorem h12ConcreteRadius_zero : h12ConcreteRadius 0 = 1 / 64 := by
  norm_num [h12ConcreteRadius, h12BoxRadius]

theorem h12ConcreteRadius_34 : h12ConcreteRadius 34 = 1 / 128 := by
  norm_num [h12ConcreteRadius, h12BoxRadius, h12ConcreteDelta]

theorem h12ConcreteRadius_add_one (j : ℝ) :
    h12ConcreteRadius (j + 1) = h12ConcreteRadius j - h12ConcreteDelta := by
  simp only [h12ConcreteRadius_eq]
  ring

theorem h12ConcreteRadius_add_two (j : ℝ) :
    h12ConcreteRadius (j + 2) = h12ConcreteRadius j - 2 * h12ConcreteDelta := by
  simp only [h12ConcreteRadius_eq]
  ring

theorem h12ConcreteRadius_antitone : Antitone h12ConcreteRadius := by
  intro j k hjk
  simp only [h12ConcreteRadius_eq]
  exact sub_le_sub_left (mul_le_mul_of_nonneg_right hjk h12ConcreteDelta_pos.le) _

theorem h12ConcreteRadius_two_gap {j : ℝ} (hj : j ≤ 32) :
    2 * h12ConcreteDelta ≤ h12ConcreteRadius j := by
  have h := h12ConcreteRadius_antitone hj
  norm_num [h12ConcreteRadius, h12BoxRadius, h12ConcreteDelta] at h ⊢
  linarith

theorem h12ConcreteRadius_le_outer {j : ℝ} (hj : 0 ≤ j) :
    h12ConcreteRadius j ≤ 1 / 64 := by
  simpa only [h12ConcreteRadius_zero] using h12ConcreteRadius_antitone hj

theorem h12ConcreteRadius_ge_inner {j : ℝ} (hj : j ≤ 34) :
    1 / 128 ≤ h12ConcreteRadius j := by
  simpa only [h12ConcreteRadius_34] using h12ConcreteRadius_antitone hj

theorem h12ConcreteRadius_pos {j : ℝ} (hj : j ≤ 34) : 0 < h12ConcreteRadius j :=
  lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 128) (h12ConcreteRadius_ge_inner hj)

theorem h12ConcreteBox_eq_rectangularOpenBox (center : Space (Fin 3)) (j : ℝ) :
    h12ConcreteBox center j =
      rectangularOpenBox center (h12ConcreteRadius j) (h12ConcreteRadius j) := rfl

theorem h12ConcreteBox_zero (center : Space (Fin 3)) :
    h12ConcreteBox center 0 = rectangularOpenBox center (1 / 64) (1 / 64) := by
  rw [h12ConcreteBox_eq_rectangularOpenBox, h12ConcreteRadius_zero]

theorem h12ConcreteBox_34 (center : Space (Fin 3)) :
    h12ConcreteBox center 34 = rectangularOpenBox center (1 / 128) (1 / 128) := by
  rw [h12ConcreteBox_eq_rectangularOpenBox, h12ConcreteRadius_34]

theorem h12ConcreteBox_isOpen (center : Space (Fin 3)) (j : ℝ) :
    IsOpen (h12ConcreteBox center j) := h12ScheduledBox_isOpen center _ _ _ _

theorem h12ConcreteBox_measurableSet (center : Space (Fin 3)) (j : ℝ) :
    MeasurableSet (h12ConcreteBox center j) := (h12ConcreteBox_isOpen center j).measurableSet

theorem h12ConcreteBox_antitone (center : Space (Fin 3)) :
    Antitone (h12ConcreteBox center) := by
  intro j k hjk p hp d
  cases d with
  | inl d => exact (hp (.inl d)).trans_le (h12ConcreteRadius_antitone hjk)
  | inr d => exact (hp (.inr d)).trans_le (h12ConcreteRadius_antitone hjk)

theorem h12ConcreteBox_subset_outer (center : Space (Fin 3)) {j : ℝ} (hj : 0 ≤ j) :
    h12ConcreteBox center j ⊆ rectangularOpenBox center (1 / 64) (1 / 64) := by
  simpa only [h12ConcreteBox_zero] using h12ConcreteBox_antitone center hj

theorem h12ConcreteBox_y_radius (center : Space (Fin 3)) {j : ℝ} (hj : 0 ≤ j)
    {p : Space (Fin 3)} (hp : p ∈ h12ConcreteBox center j) :
    ‖p.1‖ ≤ ‖center.1‖ + 1 / 32 := by
  have h := h12ScheduledBox_y_radius center h12ConcreteDelta_pos.le hj hp
  norm_num at h ⊢
  exact h

end TheoremT.Continuum.WeakGrushin
