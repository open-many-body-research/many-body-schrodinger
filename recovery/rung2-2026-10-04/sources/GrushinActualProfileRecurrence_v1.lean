import GrushinActualProfileLocalizedBound_v1
import GrushinLocalizedScalarAbsorption_v1

/-! R18 for actual local weighted derivative norms of one coherent weak
solution family. The recurrence is a conclusion of the original equation,
finite local weak regularity and analytic coefficient/source data. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
set_option maxRecDepth 8192
namespace TheoremT.Continuum.WeakGrushin

def factorialProfileRecurrenceConstant (c aY ρ C1 C2 M : ℝ) : ℝ :=
  grushinLocalizedCoefficient (factorialProfileGraphConstant c aY) M c
    (factorialProfileCutoffFirst c aY ρ C1) (factorialProfileCutoffSecond c aY ρ C1 C2)

theorem factorial_actual_profile_recurrence
    (a : Space (Fin 3)) (ha : a.1 = 0) (c : ℝ) (hcpos : 0 < c)
    {aY aT ρ C1 C2 : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (hρy : ρ < aY) (hρt : ρ < aT)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    (F : FactorialRawJetFamily)
    (hreg : ∀ m : ℕ, ∃ W : ℝ, 0 ≤ W ∧ ∀ α β,
      (∑ i,α i)+(∑ j,β j) ≤ m → RegionL2Budget (F α β) (rectangularOpenBox a aY aT) W)
    (hY : ∀ α β i, ProductLocalWeakDirectional (rectangularOpenBox a aY aT)
      (F α β) (F (α+Pi.single i 1) β) (yDir i))
    (hT : ∀ α β j, ProductLocalWeakDirectional (rectangularOpenBox a aY aT)
      (F α β) (F α (β+Pi.single j 1)) (tDir j))
    (B : Space (Fin 3) → ℝ) (src : Space (Fin 3) → ℂ)
    (hB : ContDiffOn ℝ ∞ B (rectangularOpenBox a aY aT))
    (hsrc : ContDiffOn ℝ ∞ src (rectangularOpenBox a aY aT))
    (M A F0 : ℝ) (hM : 0 ≤ M) (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (hBb : ∀ w, ∀ p ∈ rectangularOpenBox a aY aT,
      |directionalWordDeriv productCoordinateDirection B w p| ≤ M*A^w.length*(w.length.factorial : ℝ))
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox a aY aT →
      (∫ p, splitGrushin c oscillatorBasis B φ p • F 0 0 p) = ∫ p,φ p • src p)
    (hSourceBudget : ∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection src w)
        (rectangularOpenBox a aY aT) ((F0*A^w.length*(w.length.factorial : ℝ))^2)) :
    GrushinScalarFixedGapRecurrence (factorialBoxProfile F a aY aT) ρ
      (factorialProfileRecurrenceConstant c aY ρ C1 C2 M) A F0 := by
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have hC20 : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  have hY0 : 0 < aY := hρ.trans hρy
  have hC0 : 0 ≤ factorialProfileGraphConstant c aY := by
    unfold factorialProfileGraphConstant
    positivity
  have hK1 : 0 ≤ factorialProfileCutoffFirst c aY ρ C1 := by
    unfold factorialProfileCutoffFirst
    positivity
  have hK2 : 0 ≤ factorialProfileCutoffSecond c aY ρ C1 C2 := by
    unfold factorialProfileCutoffSecond
    positivity
  apply grushin_fixed_gap_recurrence_of_localized_bounds
    (factorialBoxProfile F a aY aT) c hρ1 hA hC0 hM hK1 hK2 hF0
    (fun q s _ _ => factorialBoxProfile_nonneg F a aY aT q s)
  intro r hr t e ht he hte
  have hsub : rectangularOpenBox a (aY-t) (aT-t) ⊆ rectangularOpenBox a aY aT := by
    simpa only [factorialProfileBox,sub_zero] using factorialProfileBox_antitone a aY aT ht
  obtain ⟨W,hW,hF⟩ := hreg (r+2)
  have hb := factorial_actual_profile_localized_bound a ha c hcpos he ht hte hρy hρt
    hC1 hC2 r (by omega) W F
    (fun α β hdegree => (hF α β hdegree).restrict hsub le_rfl)
    (fun α β i _ => (hY α β i).mono hsub)
    (fun α β j _ => (hT α β j).mono hsub)
    B src (hB.mono hsub) (hsrc.mono hsub) M A F0 hM hA hF0
    (fun w _ p hp => hBb w p (hsub hp))
    (fun φ hφ hcφ hsφ => hP φ hφ hcφ (hsφ.trans hsub)) hSourceBudget
  convert hb using 1 <;>
    simp only [factorialProfileCutoffFirst,factorialProfileCutoffSecond,div_eq_mul_inv,inv_pow] <;> ring

end TheoremT.Continuum.WeakGrushin
