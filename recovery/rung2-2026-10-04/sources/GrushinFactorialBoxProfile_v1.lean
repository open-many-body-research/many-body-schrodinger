import GrushinFactorialLocalRepresentatives_v1
import RestrictedCompactWeightMemLp_v1

/-! Actual shrinking rectangular-box profiles. Finite unweighted local
jet membership through order r+2 proves membership of every shifted weighted
component in N_r. The same actual family is used at every radius. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

def factorialProfileBox (a : Space (Fin 3)) (aY aT s : ℝ) : Set (Space (Fin 3)) :=
  rectangularOpenBox a (aY-s) (aT-s)

def factorialBoxProfile (D : FactorialRawJetFamily) (a : Space (Fin 3))
    (aY aT : ℝ) (r : ℕ) (s : ℝ) : ℝ :=
  factorialLocalProfile D (factorialProfileBox a aY aT s) r

theorem factorialProfileBox_antitone (a : Space (Fin 3)) (aY aT : ℝ)
    {s t : ℝ} (hst : s ≤ t) : factorialProfileBox a aY aT t ⊆ factorialProfileBox a aY aT s := by
  intro p hp i
  cases i with
  | inl i => exact (hp (.inl i)).trans_le (sub_le_sub_left hst aY)
  | inr j => exact (hp (.inr j)).trans_le (sub_le_sub_left hst aT)

theorem factorial_shifted_total_le {r : ℕ}
    (a : Fin 4 → ℕ) (b : Fin 3 → ℕ) (hab : factorialMultiDerivativeCost a b ≤ r)
    (m : FactorialOuterIndex) (hm : m ∈ factorialOuterIndices) :
    (∑ i, (a+m.1) i)+(∑ j, (b+m.2.1) j) ≤ r+2 := by
  have hc := factorialDerivativeCost_total_le (∑ i,a i) (∑ j,b j)
  change (∑ i,a i)+(∑ j,b j) ≤ factorialMultiDerivativeCost a b at hc
  have ho := ((factorialOuterIndices_mem m).mp hm).1
  simp only [Pi.add_apply,Finset.sum_add_distrib]
  omega

theorem factorialLocalMemLp_rectangular
    (D : FactorialRawJetFamily) (a : Space (Fin 3)) {aY aT : ℝ}
    (hY : 0 ≤ aY) (hT : 0 ≤ aT) {r m : ℕ} (hrm : r+2 ≤ m)
    (hF : ∀ α β, (∑ i,α i)+(∑ j,β j) ≤ m →
      MemLp (D α β) 2 (volume.restrict (rectangularOpenBox a aY aT))) :
    FactorialLocalMemLp D (rectangularOpenBox a aY aT) r := by
  intro α β hab k hk
  exact rectangular_factorial_monomial_memLp a hY hT k.2.2
    (hF (α+k.1) (β+k.2.1) ((factorial_shifted_total_le α β hab k hk).trans hrm))

theorem factorialProfileBox_memLp_of_all_finite_budgets
    (D : FactorialRawJetFamily) (a : Space (Fin 3)) {aY aT : ℝ}
    (hY : 0 ≤ aY) (hT : 0 ≤ aT)
    (hreg : ∀ m : ℕ, ∃ W : ℝ, 0 ≤ W ∧ ∀ α β,
      (∑ i,α i)+(∑ j,β j) ≤ m → RegionL2Budget (D α β) (rectangularOpenBox a aY aT) W)
    (r : ℕ) (s : ℝ) (hs : 0 ≤ s) :
    FactorialLocalMemLp D (factorialProfileBox a aY aT s) r := by
  obtain ⟨W,hW,hb⟩ := hreg (r+2)
  have hzero := factorialLocalMemLp_rectangular D a hY hT le_rfl (fun α β ho => (hb α β ho).1)
  have hsub : factorialProfileBox a aY aT s ⊆ rectangularOpenBox a aY aT := by
    simpa only [factorialProfileBox,sub_zero] using factorialProfileBox_antitone a aY aT hs
  exact hzero.restrict hsub

theorem factorialBoxProfile_nonneg (D : FactorialRawJetFamily) (a : Space (Fin 3))
    (aY aT : ℝ) (r : ℕ) (s : ℝ) : 0 ≤ factorialBoxProfile D a aY aT r s :=
  factorialLocalProfile_nonneg D _ r

theorem factorialBoxProfile_antitone_of_all_finite_budgets
    (D : FactorialRawJetFamily) (a : Space (Fin 3)) {aY aT : ℝ}
    (hY : 0 ≤ aY) (hT : 0 ≤ aT)
    (hreg : ∀ m : ℕ, ∃ W : ℝ, 0 ≤ W ∧ ∀ α β,
      (∑ i,α i)+(∑ j,β j) ≤ m → RegionL2Budget (D α β) (rectangularOpenBox a aY aT) W)
    (r : ℕ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    factorialBoxProfile D a aY aT r t ≤ factorialBoxProfile D a aY aT r s :=
  factorialLocalProfile_mono_domain
    (factorialProfileBox_memLp_of_all_finite_budgets D a hY hT hreg r s hs)
    (factorialProfileBox_antitone a aY aT hst)

end TheoremT.Continuum.WeakGrushin
