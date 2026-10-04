import WeakGrushinSpectatorForcingJet_v1

/-! Ordered spectator words and their exact Leibniz choices.  Multiplicity is
retained: equal directions do not collapse distinct choices.  Proper choices
differentiate the coefficient at least once and use a strictly shorter
solution word.  No regularity of a solution is defined by these combinatorics. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin

def spectatorWordSplits {κ : Type} : List κ → List (List κ × List κ)
  | [] => [([],[])]
  | j :: w => (spectatorWordSplits w).map (fun ab => (j :: ab.1, ab.2)) ++
      (spectatorWordSplits w).map (fun ab => (ab.1, j :: ab.2))

def spectatorWordProperSplits {κ : Type} : List κ → List (List κ × List κ)
  | [] => []
  | j :: w => (spectatorWordSplits w).map (fun ab => (j :: ab.1, ab.2)) ++
      (spectatorWordProperSplits w).map (fun ab => (ab.1, j :: ab.2))

theorem spectatorWordSplits_eq_proper_append {κ : Type} (w : List κ) :
    spectatorWordSplits w = spectatorWordProperSplits w ++ [([],w)] := by
  induction w with
  | nil => rfl
  | cons j w ih =>
    simp only [spectatorWordSplits, spectatorWordProperSplits]
    rw [ih]
    simp only [List.map_append, List.map_cons, List.map_nil, List.append_assoc]

theorem spectatorWordSplits_length {κ : Type} (w : List κ) :
    (spectatorWordSplits w).length = 2 ^ w.length := by
  induction w with
  | nil => simp [spectatorWordSplits]
  | cons j w ih => simp [spectatorWordSplits, ih, pow_succ, Nat.mul_two]

theorem spectatorWordProperSplits_length {κ : Type} (w : List κ) :
    (spectatorWordProperSplits w).length + 1 = 2 ^ w.length := by
  have h := spectatorWordSplits_length w
  rw [spectatorWordSplits_eq_proper_append] at h
  simpa using h

theorem spectatorWordSplits_length_sum {κ : Type} {w : List κ}
    {ab : List κ × List κ} (hab : ab ∈ spectatorWordSplits w) :
    ab.1.length + ab.2.length = w.length := by
  induction w generalizing ab with
  | nil =>
    have he : ab = ([],[]) := by simpa [spectatorWordSplits] using hab
    simp [he]
  | cons j w ih =>
    simp only [spectatorWordSplits, List.mem_append, List.mem_map] at hab
    rcases hab with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩ <;> have hi := ih ha <;>
      simp only [List.length_cons] <;> omega

theorem spectatorWordProperSplits_strict {κ : Type} {w : List κ}
    {ab : List κ × List κ} (hab : ab ∈ spectatorWordProperSplits w) :
    0 < ab.1.length ∧ ab.2.length < w.length ∧
      ab.1.length + ab.2.length = w.length := by
  induction w generalizing ab with
  | nil => simp [spectatorWordProperSplits] at hab
  | cons j w ih =>
    simp only [spectatorWordProperSplits, List.mem_append, List.mem_map] at hab
    rcases hab with ⟨a,ha,rfl⟩ | ⟨a,ha,rfl⟩
    · have hi := spectatorWordSplits_length_sum ha
      simp only [List.length_cons]
      omega
    · have hi := ih ha
      simp only [List.length_cons]
      omega

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def spectatorWordDeriv (B : Space κ → ℝ) : List κ → Space κ → ℝ
  | [] => B
  | j :: w => fun p => fderiv ℝ (spectatorWordDeriv B w) p (tDir j)

theorem spectatorWordDeriv_contDiffOn {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) (w : List κ) :
    ContDiffOn ℝ ∞ (spectatorWordDeriv B w) Ω := by
  induction w with
  | nil => exact hB
  | cons j w ih => exact spectator_potential_coefficient_contDiffOn hΩ ih j

#print axioms spectatorWordSplits_eq_proper_append
#print axioms spectatorWordSplits_length
#print axioms spectatorWordProperSplits_length
#print axioms spectatorWordSplits_length_sum
#print axioms spectatorWordProperSplits_strict
#print axioms spectatorWordDeriv_contDiffOn
end TheoremT.Continuum.WeakGrushin
