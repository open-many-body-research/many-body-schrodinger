import GrushinActualProfileRecurrence_v1
import GrushinScalarFixedGapBound_v1
import FactorialCenteredBoxBaseProfile_v1

/-! R23 for the literal actual weighted profile. The original weak PDE,
coefficient/source bounds and one genuine finite H12 budget imply the bound;
recurrence, profile monotonicity and the base estimate are all derived. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
set_option maxRecDepth 8192
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_actual_profile_R23_bound
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
    (potential : Space (Fin 3) → ℝ) (src : Space (Fin 3) → ℂ)
    (hB : ContDiffOn ℝ ∞ potential (rectangularOpenBox a aY aT))
    (hsrc : ContDiffOn ℝ ∞ src (rectangularOpenBox a aY aT))
    (M A F0 : ℝ) (hM : 0 ≤ M) (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (hBb : ∀ w, ∀ p ∈ rectangularOpenBox a aY aT,
      |directionalWordDeriv productCoordinateDirection potential w p| ≤ M*A^w.length*(w.length.factorial : ℝ))
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox a aY aT →
      (∫ p, splitGrushin c oscillatorBasis potential φ p • F 0 0 p) = ∫ p,φ p • src p)
    (hSourceBudget : ∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection src w)
        (rectangularOpenBox a aY aT) ((F0*A^w.length*(w.length.factorial : ℝ))^2))
    (W : ℝ)
    (h12 : ProductMixedMultiIndexWeakHk (rectangularOpenBox a aY aT) (F 0 0) 12 W)
    (r : ℕ) :
    let C := factorialProfileRecurrenceConstant c aY ρ C1 C2 M
    let H0 := 498*(max 1 (2*aY))^2*Real.sqrt W
    let B := 2*C*A
    factorialBoxProfile F a aY aT r ρ ≤ 2*B*(F0+H0)*(2*B*((r : ℝ)+1)/ρ)^r := by
  have hYpos : 0 < aY := hρ.trans hρy
  have hTpos : 0 < aT := hρ.trans hρt
  have hrec := factorial_actual_profile_recurrence a ha c hcpos hρ hρ1 hρy hρt
    hC1 hC2 F hreg hY hT potential src hB hsrc M A F0 hM hA hF0 hBb hP hSourceBudget
  have hC : 1 ≤ factorialProfileRecurrenceConstant c aY ρ C1 C2 M := by
    unfold factorialProfileRecurrenceConstant grushinLocalizedCoefficient
    exact le_max_left _ _
  have hH0 : 0 ≤ 498*(max 1 (2*aY))^2*Real.sqrt W := by positivity
  apply grushin_scalar_fixed_gap_bound (factorialBoxProfile F a aY aT)
    hρ hρ1 hC hA hF0 hH0
    (fun q s _ _ => factorialBoxProfile_nonneg F a aY aT q s)
    (fun q s t hs hst _ => factorialBoxProfile_antitone_of_all_finite_budgets
      F a hYpos.le hTpos.le hreg q hs hst)
    ?_ hrec r
  intro q hq s hs _
  exact (factorial_centered_box_base_profile_of_H12 a ha hYpos hTpos F h12 hY hT q hq s hs).2

theorem factorial_actual_profile_R23_representatives
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
    (potential : Space (Fin 3) → ℝ) (src : Space (Fin 3) → ℂ)
    (hB : ContDiffOn ℝ ∞ potential (rectangularOpenBox a aY aT))
    (hsrc : ContDiffOn ℝ ∞ src (rectangularOpenBox a aY aT))
    (M A F0 : ℝ) (hM : 0 ≤ M) (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (hBb : ∀ w, ∀ p ∈ rectangularOpenBox a aY aT,
      |directionalWordDeriv productCoordinateDirection potential w p| ≤ M*A^w.length*(w.length.factorial : ℝ))
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox a aY aT →
      (∫ p, splitGrushin c oscillatorBasis potential φ p • F 0 0 p) = ∫ p,φ p • src p)
    (hSourceBudget : ∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection src w)
        (rectangularOpenBox a aY aT) ((F0*A^w.length*(w.length.factorial : ℝ))^2))
    (W : ℝ)
    (h12 : ProductMixedMultiIndexWeakHk (rectangularOpenBox a aY aT) (F 0 0) 12 W)
    (r : ℕ) :
    let C := factorialProfileRecurrenceConstant c aY ρ C1 C2 M
    let H0 := 498*(max 1 (2*aY))^2*Real.sqrt W
    let B := 2*C*A
    FactorialLocalMemLp F (factorialProfileBox a aY aT ρ) r ∧
    ∃ V : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex →
      Lp ℂ 2 (volume.restrict (factorialProfileBox a aY aT ρ)),
      ∀ α β, factorialMultiDerivativeCost α β ≤ r →
        FactorialShiftedOuterL2Rep F V α β ∧
        factorialOuterNorm (V α β) =
          factorialLocalOuterNorm F (factorialProfileBox a aY aT ρ) α β ∧
        factorialOuterNorm (V α β) ≤ 2*B*(F0+H0)*(2*B*((r : ℝ)+1)/ρ)^r := by
  have hfinite := factorialProfileBox_memLp_of_all_finite_budgets F a
    (hρ.trans hρy).le (hρ.trans hρt).le hreg r ρ hρ.le
  obtain ⟨V,hV⟩ := factorialLocalProfile_representatives hfinite
  have hbound := factorial_actual_profile_R23_bound a ha c hcpos hρ hρ1 hρy hρt
    hC1 hC2 F hreg hY hT potential src hB hsrc M A F0 hM hA hF0 hBb hP hSourceBudget W h12 r
  refine ⟨hfinite,V,?_⟩
  intro α β hab
  exact ⟨(hV α β hab).1,(hV α β hab).2.1,(hV α β hab).2.2.trans hbound⟩

end TheoremT.Continuum.WeakGrushin
