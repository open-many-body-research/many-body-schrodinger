import GrushinActualProfileBound_v1
import ProductMixedAllOrderWeakFamily_v1

/-! Quantitative actual local profile bound from the original weak equation.
The solution is locally L2 and has one supplied genuine H12 budget. All
higher weak jets, their coherent choice, the localized recurrence, and its
solution are conclusions. Smoothness and factorial bounds apply only to the
known coefficient/source data. No classical solution representative or
executable construction is asserted. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
set_option maxRecDepth 8192
namespace TheoremT.Continuum.WeakGrushin

theorem local_weak_grushin_raw_profile_bound
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    (a : Space (Fin 3)) (ha : a.1 = 0) {aY aT bY bT ρ c C1 C2 : ℝ}
    (hy : bY < aY) (ht : bT < aT)
    (hKΩ : rectangularClosedBox a aY aT ⊆ Ω) (hc : 0 < c)
    (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (hρy : ρ < bY) (hρt : ρ < bT)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    {potential : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ potential Ω)
    {src : Space (Fin 3) → ℂ} (hs : ContDiffOn ℝ ∞ src Ω)
    {f : Space (Fin 3) → ℂ} (hf : ProductLocallyL2On f Ω)
    (hEq : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis potential φ p • f p) = ∫ p,φ p • src p)
    (M A F0 : ℝ) (hM : 0 ≤ M) (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (hBb : ∀ w, ∀ p ∈ rectangularOpenBox a bY bT,
      |directionalWordDeriv productCoordinateDirection potential w p| ≤ M*A^w.length*(w.length.factorial : ℝ))
    (hSourceBudget : ∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection src w)
        (rectangularOpenBox a bY bT) ((F0*A^w.length*(w.length.factorial : ℝ))^2))
    (W : ℝ) (h12 : ProductMixedMultiIndexWeakHk (rectangularOpenBox a bY bT) f 12 W) :
    ∃ F : FactorialRawJetFamily, F 0 0 = f ∧
      (∀ m : ℕ, ∃ V : ℝ, 0 ≤ V ∧ ∀ α β,
        (∑ i,α i)+(∑ j,β j) ≤ m → RegionL2Budget (F α β) (rectangularOpenBox a bY bT) V) ∧
      (∀ α β i, ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
        (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
      (∀ α β j, ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
        (F α β) (F α (β+Pi.single j 1)) (tDir j)) ∧
      ∀ r : ℕ,
        FactorialLocalMemLp F (factorialProfileBox a bY bT ρ) r ∧
        let C := factorialProfileRecurrenceConstant c bY ρ C1 C2 M
        let H0 := 498*(max 1 (2*bY))^2*Real.sqrt W
        let B := 2*C*A
        factorialBoxProfile F a bY bT r ρ ≤ 2*B*(F0+H0)*(2*B*((r : ℝ)+1)/ρ)^r := by
  obtain ⟨F,h0,hreg,hY,hT⟩ := local_smooth_weak_grushin_allOrder_family
    hΩ a (hρ.trans hρy) (hρ.trans hρt) hy ht hKΩ hc hB hs hf hEq
  have hInner : rectangularOpenBox a bY bT ⊆ Ω :=
    (rectangularOpenBox_subset_closedBox a bY bT).trans
      ((rectangularClosedBox_subset_openBox a hy ht).trans
        ((rectangularOpenBox_subset_closedBox a aY aT).trans hKΩ))
  have hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox a bY bT →
      (∫ p, splitGrushin c oscillatorBasis potential φ p • F 0 0 p) = ∫ p,φ p • src p := by
    intro φ hφ hcφ hsφ
    simpa only [h0] using hEq φ hφ hcφ (hsφ.trans hInner)
  have hF12 : ProductMixedMultiIndexWeakHk (rectangularOpenBox a bY bT) (F 0 0) 12 W := by
    simpa only [h0] using h12
  refine ⟨F,h0,hreg,hY,hT,?_⟩
  intro r
  refine ⟨factorialProfileBox_memLp_of_all_finite_budgets F a
    (hρ.trans hρy).le (hρ.trans hρt).le hreg r ρ hρ.le,?_⟩
  exact factorial_actual_profile_R23_bound a ha c hc hρ hρ1 hρy hρt hC1 hC2
    F hreg hY hT potential src (hB.mono hInner) (hs.mono hInner)
    M A F0 hM hA hF0 hBb hP hSourceBudget W hF12 r

end TheoremT.Continuum.WeakGrushin
