import FactorialR9BaseProfile_v1
import GrushinFactorialBoxProfile_v1

/-! The centered rectangular box supplies its own Euclidean Y radius.
A genuine finite weak H12 budget controls every base profile through order
eight on every nonnegative shrink of the same box and same raw jet family.
Actual weighted L2 membership is part of the conclusion. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators

namespace TheoremT.Continuum.WeakGrushin

theorem factorial_centered_box_base_profile_of_H12
    (a : Space (Fin 3)) (ha : a.1 = 0) {aY aT W : ℝ}
    (hY : 0 < aY) (hT : 0 < aT) (F : FactorialRawJetFamily)
    (hf : ProductMixedMultiIndexWeakHk (rectangularOpenBox a aY aT) (F 0 0) 12 W)
    (hFY : ∀ α β i, ProductLocalWeakDirectional (rectangularOpenBox a aY aT)
      (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hFT : ∀ α β j, ProductLocalWeakDirectional (rectangularOpenBox a aY aT)
      (F α β) (F α (β+Pi.single j 1)) (tDir j)) :
    ∀ r : ℕ, r ≤ 8 → ∀ s : ℝ, 0 ≤ s →
      FactorialLocalMemLp F (factorialProfileBox a aY aT s) r ∧
      factorialBoxProfile F a aY aT r s ≤ 498*(max 1 (2*aY))^2*Real.sqrt W := by
  have hrad : ∀ p ∈ rectangularOpenBox a aY aT, ‖p.1‖ ≤ max 1 (2*aY) := by
    intro p hp
    have hb := rectangularClosedBox_y_radius a hY.le
      (rectangularOpenBox_subset_closedBox a aY aT hp)
    have hy : ‖p.1‖ ≤ 2*aY := by
      simpa only [ha,norm_zero,zero_add] using hb
    exact hy.trans (le_max_right 1 (2*aY))
  have hbase := factorial_R9_base_profile_of_H12 (rectangularOpenBox_isOpen a aY aT)
    hf F (Eventually.of_forall (fun _ _ => rfl))
    (fun α β i _ => hFY α β i) (fun α β j _ => hFT α β j)
    (le_max_left 1 (2*aY)) hrad
  intro r hr s hs
  have hsub : factorialProfileBox a aY aT s ⊆ rectangularOpenBox a aY aT := by
    simpa only [factorialProfileBox,sub_zero] using factorialProfileBox_antitone a aY aT hs
  obtain ⟨hmem,hbound,_⟩ := hbase r hr (factorialProfileBox a aY aT s) hsub
  exact ⟨hmem,hbound⟩

end TheoremT.Continuum.WeakGrushin
