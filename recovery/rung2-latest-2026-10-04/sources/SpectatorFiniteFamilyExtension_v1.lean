import LocalSpectatorDerivativeAlgebra_v1

/-! Finite family gluing on a smaller region.  Genuine top-order derivative
witnesses are supplied to this elementary gluing lemma; the next module
constructs them from the Grushin equation and the existing one-step gain. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def spectatorFamilyExtend (G : List κ → Space κ → ℂ)
    (T : List κ → κ → Space κ → ℂ) (m : ℕ) : List κ → Space κ → ℂ
  | [] => G []
  | j :: w => if w.length < m then G (j :: w) else T w j

theorem spectatorFamilyExtend_old (G : List κ → Space κ → ℂ)
    (T : List κ → κ → Space κ → ℂ) (m : ℕ) (w : List κ) (hw : w.length ≤ m) :
    spectatorFamilyExtend G T m w = G w := by
  cases w with
  | nil => rfl
  | cons j w =>
    have hn : w.length < m := by simp only [List.length_cons] at hw; omega
    simp only [spectatorFamilyExtend, if_pos hn]

theorem spectatorFamilyExtend_top (G : List κ → Space κ → ℂ)
    (T : List κ → κ → Space κ → ℂ) (m : ℕ) (w : List κ) (j : κ)
    (hw : w.length = m) : spectatorFamilyExtend G T m (j :: w) = T w j := by
  simp [spectatorFamilyExtend, hw]

theorem spectatorFamilyExtend_genuine
    {V : Set (Space κ)} (G : List κ → Space κ → ℂ)
    (T : List κ → κ → Space κ → ℂ) (m : ℕ)
    (hG : ∀ w, w.length ≤ m → ProductLocallyL2On (G w) V)
    (hD : ∀ w j, w.length < m → LocalSpectatorD V (G w) (G (j :: w)) j)
    (hT : ∀ w j, w.length = m → ProductLocallyL2On (T w j) V)
    (hTD : ∀ w j, w.length = m → LocalSpectatorD V (G w) (T w j) j) :
    (∀ w, w.length ≤ m+1 → ProductLocallyL2On (spectatorFamilyExtend G T m w) V) ∧
    ∀ w j, w.length < m+1 →
      LocalSpectatorD V (spectatorFamilyExtend G T m w)
        (spectatorFamilyExtend G T m (j :: w)) j := by
  constructor
  · intro w hw
    by_cases hold : w.length ≤ m
    · rw [spectatorFamilyExtend_old G T m w hold]
      exact hG w hold
    · cases w with
      | nil => simp at hold
      | cons j w =>
        have ht : w.length = m := by simp only [List.length_cons] at hw hold; omega
        rw [spectatorFamilyExtend_top G T m w j ht]
        exact hT w j ht
  · intro w j hw
    have hold : w.length ≤ m := by omega
    rw [spectatorFamilyExtend_old G T m w hold]
    by_cases hlt : w.length < m
    · rw [spectatorFamilyExtend_old G T m (j :: w)
        (by simp only [List.length_cons]; omega)]
      exact hD w j hlt
    · have ht : w.length = m := by omega
      rw [spectatorFamilyExtend_top G T m w j ht]
      exact hTD w j ht

#print axioms spectatorFamilyExtend_old
#print axioms spectatorFamilyExtend_top
#print axioms spectatorFamilyExtend_genuine
end TheoremT.Continuum.WeakGrushin
