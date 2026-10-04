import LocalWeakGrushinRawProfileBound_v1
import GrushinSuccessorPowerFactorial_v1

/-! An actual weighted L2 factorial bound for weak local Grushin solutions.
The only solution-regularity input beyond local L2 is one genuine finite H12
budget. Known data carry the analytic bounds; all higher weak derivatives
and their quantitative bounds are constructed from the original equation.
This is not yet a pointwise analytic representative or KS descent theorem. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
set_option maxRecDepth 8192
namespace TheoremT.Continuum.WeakGrushin

theorem local_weak_grushin_raw_factorial_bound
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
        factorialBoxProfile F a bY bT r ρ ≤ 6*B*(F0+H0)*(6*B/ρ)^r*(r.factorial : ℝ) := by
  obtain ⟨F,h0,hreg,hY,hT,hbound⟩ := local_weak_grushin_raw_profile_bound hΩ a ha
    hy ht hKΩ hc hρ hρ1 hρy hρt hC1 hC2 hB hs hf hEq M A F0 hM hA hF0 hBb hSourceBudget W h12
  refine ⟨F,h0,hreg,hY,hT,?_⟩
  intro r
  refine ⟨(hbound r).1,?_⟩
  let C := factorialProfileRecurrenceConstant c bY ρ C1 C2 M
  let H0 := 498*(max 1 (2*bY))^2*Real.sqrt W
  let B := 2*C*A
  have hC : 1 ≤ C := le_max_left _ _
  have hB0 : 0 ≤ B := by
    have hA0 := zero_le_one.trans hA
    have hC0 := zero_le_one.trans hC
    dsimp [B]
    positivity
  have hS : 0 ≤ F0+H0 := by dsimp [H0]; positivity
  exact grushin_r23_factorial_bound r hρ hB0 hS (hbound r).2

end TheoremT.Continuum.WeakGrushin
