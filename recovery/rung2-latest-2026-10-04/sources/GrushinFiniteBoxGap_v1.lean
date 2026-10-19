import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! A solution-independent scalar gap for any finite number of two-gap
Grushin stages. The denominator reserves two extra gaps after the last stage,
so the final half-widths remain strictly larger than the requested inner ones.
No box, differential-equation or regularity assertion is included. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin

def finiteGrushinGap (aY aT bY bT : ℝ) (n : ℕ) : ℝ :=
  min (aY - bY) (aT - bT) / (2 * ((n : ℝ) + 1))

theorem finiteGrushinGap_pos {aY aT bY bT : ℝ} (n : ℕ)
    (hy : bY < aY) (ht : bT < aT) : 0 < finiteGrushinGap aY aT bY bT n := by
  unfold finiteGrushinGap
  exact div_pos (lt_min (sub_pos.mpr hy) (sub_pos.mpr ht)) (by positivity)

theorem finiteGrushinGap_scaled (aY aT bY bT : ℝ) (n : ℕ) :
    (2 * ((n : ℝ) + 1)) * finiteGrushinGap aY aT bY bT n =
      min (aY - bY) (aT - bT) := by
  have hd : (2 * ((n : ℝ) + 1)) ≠ 0 := by positivity
  unfold finiteGrushinGap
  field_simp

theorem finiteGrushinGap_y_margin (aY aT bY bT : ℝ) (n : ℕ) :
    (2 * ((n : ℝ) + 1)) * finiteGrushinGap aY aT bY bT n ≤ aY - bY := by
  rw [finiteGrushinGap_scaled]
  exact min_le_left _ _

theorem finiteGrushinGap_t_margin (aY aT bY bT : ℝ) (n : ℕ) :
    (2 * ((n : ℝ) + 1)) * finiteGrushinGap aY aT bY bT n ≤ aT - bT := by
  rw [finiteGrushinGap_scaled]
  exact min_le_right _ _

theorem finiteGrushinGap_y_strict {aY aT bY bT : ℝ} (n : ℕ)
    (hy : bY < aY) (ht : bT < aT) :
    bY < aY - 2 * (n : ℝ) * finiteGrushinGap aY aT bY bT n := by
  have hp := finiteGrushinGap_pos n hy ht
  have hm := finiteGrushinGap_y_margin aY aT bY bT n
  linarith

theorem finiteGrushinGap_t_strict {aY aT bY bT : ℝ} (n : ℕ)
    (hy : bY < aY) (ht : bT < aT) :
    bT < aT - 2 * (n : ℝ) * finiteGrushinGap aY aT bY bT n := by
  have hp := finiteGrushinGap_pos n hy ht
  have hm := finiteGrushinGap_t_margin aY aT bY bT n
  linarith

theorem finiteGrushinGap_consumed_nonneg {aY aT bY bT : ℝ} (n : ℕ)
    (hy : bY < aY) (ht : bT < aT) :
    0 ≤ 2 * (n : ℝ) * finiteGrushinGap aY aT bY bT n :=
  mul_nonneg (by positivity) (finiteGrushinGap_pos n hy ht).le

theorem finiteGrushinGap_y_consumed_le {aY aT bY bT : ℝ} (n : ℕ)
    (hby : 0 < bY) (hy : bY < aY) (ht : bT < aT) :
    2 * (n : ℝ) * finiteGrushinGap aY aT bY bT n ≤ aY := by
  have h := finiteGrushinGap_y_strict n hy ht
  linarith

theorem finiteGrushinGap_t_consumed_le {aY aT bY bT : ℝ} (n : ℕ)
    (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT) :
    2 * (n : ℝ) * finiteGrushinGap aY aT bY bT n ≤ aT := by
  have h := finiteGrushinGap_t_strict n hy ht
  linarith

theorem finiteGrushinGap_consumed_bounds {aY aT bY bT : ℝ} (n : ℕ)
    (hby : 0 < bY) (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT) :
    0 ≤ 2 * (n : ℝ) * finiteGrushinGap aY aT bY bT n ∧
    2 * (n : ℝ) * finiteGrushinGap aY aT bY bT n ≤ aY ∧
    2 * (n : ℝ) * finiteGrushinGap aY aT bY bT n ≤ aT :=
  ⟨finiteGrushinGap_consumed_nonneg n hy ht,
    finiteGrushinGap_y_consumed_le n hby hy ht,
    finiteGrushinGap_t_consumed_le n hbt hy ht⟩

end TheoremT.Continuum.WeakGrushin
