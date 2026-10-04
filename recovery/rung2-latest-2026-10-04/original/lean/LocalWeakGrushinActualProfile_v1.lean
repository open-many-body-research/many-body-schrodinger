import GrushinFactorialBoxProfile_v1
import ProductMixedAllOrderWeakFamily_v1

/-! The actual local profile from the raw smooth-coefficient weak PDE.
One coherent derivative family is chosen before all orders and radii.
Every weighted profile component is genuinely L2; no hypothetical profile
or uniform-in-order derivative estimate is a premise. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem local_smooth_weak_grushin_actual_box_profile
    {Ω : Set (Space (Fin 3))} (hΩ : IsOpen Ω)
    (a : Space (Fin 3)) {aY aT bY bT c : ℝ}
    (hby : 0 < bY) (hbt : 0 < bT) (hy : bY < aY) (ht : bT < aT)
    (hKΩ : rectangularClosedBox a aY aT ⊆ Ω) (hc : 0 < c)
    {B : Space (Fin 3) → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    {source : Space (Fin 3) → ℂ} (hsource : ContDiffOn ℝ ∞ source Ω)
    {f : Space (Fin 3) → ℂ} (hf : ProductLocallyL2On f Ω)
    (hEq : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis B φ p • f p) = ∫ p, φ p • source p) :
    ∃ F : FactorialRawJetFamily,
      F 0 0 = f ∧
      (∀ m : ℕ, ∃ W : ℝ, 0 ≤ W ∧ ∀ α β,
        (∑ i,α i)+(∑ j,β j) ≤ m →
          RegionL2Budget (F α β) (rectangularOpenBox a bY bT) W) ∧
      (∀ α β i, ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
        (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
      (∀ α β j, ProductLocalWeakDirectional (rectangularOpenBox a bY bT)
        (F α β) (F α (β+Pi.single j 1)) (tDir j)) ∧
      (∀ r : ℕ, ∀ s : ℝ, 0 ≤ s → FactorialLocalMemLp F (factorialProfileBox a bY bT s) r) ∧
      (∀ r : ℕ, ∀ s : ℝ, 0 ≤ s → 0 ≤ factorialBoxProfile F a bY bT r s) ∧
      (∀ r : ℕ, ∀ s t : ℝ, 0 ≤ s → s ≤ t →
        factorialBoxProfile F a bY bT r t ≤ factorialBoxProfile F a bY bT r s) := by
  obtain ⟨F,h0,hreg,hY,hT⟩ := local_smooth_weak_grushin_allOrder_family
    hΩ a hby hbt hy ht hKΩ hc hB hsource hf hEq
  exact ⟨F,h0,hreg,hY,hT,
    factorialProfileBox_memLp_of_all_finite_budgets F a hby.le hbt.le hreg,
    fun r s _ => factorialBoxProfile_nonneg F a bY bT r s,
    fun r _ _ hs hst => factorialBoxProfile_antitone_of_all_finite_budgets
      F a hby.le hbt.le hreg r hs hst⟩

end TheoremT.Continuum.WeakGrushin
