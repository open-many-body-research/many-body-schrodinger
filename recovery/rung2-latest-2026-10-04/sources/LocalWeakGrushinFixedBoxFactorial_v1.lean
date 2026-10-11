import LocalWeakGrushinRawFactorialBound_v1
import SmoothTransitionExplicitBounds_v1

/-! A fixed-box specialization for the physical chart schedule. This is a
local PDE theorem, not yet an instantiation at a Coulomb wavefunction.
Outer, H12 and output half-widths are respectively 1/64, 1/128 and 1/256.
Actual C-infinity cutoff constants 96 and 14016 are proved, not inputs. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
set_option maxRecDepth 8192
namespace TheoremT.Continuum.WeakGrushin

def fixedBoxFactorialConstant (c M : ℝ) : ℝ :=
  factorialProfileRecurrenceConstant c (1/128) (1/256) 96 14016 M

theorem local_weak_grushin_fixed_box_factorial
    (t0 : Position) (c : ℝ) (hc : 0 < c)
    {potential : Space (Fin 3) → ℝ}
    (hB : ContDiffOn ℝ ∞ potential (rectangularOpenBox (0,t0) (1/64) (1/64)))
    {src : Space (Fin 3) → ℂ}
    (hs : ContDiffOn ℝ ∞ src (rectangularOpenBox (0,t0) (1/64) (1/64)))
    {f : Space (Fin 3) → ℂ}
    (hf : ProductLocallyL2On f (rectangularOpenBox (0,t0) (1/64) (1/64)))
    (hEq : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      tsupport φ ⊆ rectangularOpenBox (0,t0) (1/64) (1/64) →
      (∫ p, splitGrushin c oscillatorBasis potential φ p • f p) = ∫ p,φ p • src p)
    (M A F0 : ℝ) (hM : 0 ≤ M) (hA : 1 ≤ A) (hF0 : 0 ≤ F0)
    (hBb : ∀ w, ∀ p ∈ rectangularOpenBox (0,t0) (1/128) (1/128),
      |directionalWordDeriv productCoordinateDirection potential w p| ≤ M*A^w.length*(w.length.factorial : ℝ))
    (hSourceBudget : ∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection src w)
        (rectangularOpenBox (0,t0) (1/128) (1/128))
        ((F0*A^w.length*(w.length.factorial : ℝ))^2))
    (W : ℝ)
    (h12 : ProductMixedMultiIndexWeakHk (rectangularOpenBox (0,t0) (1/128) (1/128)) f 12 W) :
    ∃ F : FactorialRawJetFamily, F 0 0 = f ∧
      (∀ m : ℕ, ∃ V : ℝ, 0 ≤ V ∧ ∀ α β,
        (∑ i,α i)+(∑ j,β j) ≤ m →
          RegionL2Budget (F α β) (rectangularOpenBox (0,t0) (1/128) (1/128)) V) ∧
      (∀ α β i, ProductLocalWeakDirectional (rectangularOpenBox (0,t0) (1/128) (1/128))
        (F α β) (F (α+Pi.single i 1) β) (yDir i)) ∧
      (∀ α β j, ProductLocalWeakDirectional (rectangularOpenBox (0,t0) (1/128) (1/128))
        (F α β) (F α (β+Pi.single j 1)) (tDir j)) ∧
      ∀ r : ℕ,
        FactorialLocalMemLp F (rectangularOpenBox (0,t0) (1/256) (1/256)) r ∧
        let C := fixedBoxFactorialConstant c M
        factorialLocalProfile F (rectangularOpenBox (0,t0) (1/256) (1/256)) r ≤
          12*C*A*(F0+498*Real.sqrt W)*(3072*C*A)^r*(r.factorial : ℝ) := by
  obtain ⟨F,h0,hreg,hY,hT,hbound⟩ := local_weak_grushin_raw_factorial_bound
    (rectangularOpenBox_isOpen (0,t0) _ _) (0,t0) rfl
    (aY := 3/256) (aT := 3/256) (bY := 1/128) (bT := 1/128) (ρ := 1/256)
    (by norm_num) (by norm_num)
    (rectangularClosedBox_subset_openBox (0,t0) (by norm_num) (by norm_num)) hc
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    smoothTransition_deriv_abs_le_ninety_six
    smoothTransition_second_deriv_abs_le_fourteen_thousand_sixteen
    hB hs hf hEq M A F0 hM hA hF0 hBb hSourceBudget W h12
  refine ⟨F,h0,hreg,hY,hT,?_⟩
  intro r
  have hr := hbound r
  norm_num [factorialProfileBox,factorialBoxProfile] at hr
  refine ⟨hr.1,?_⟩
  dsimp only [fixedBoxFactorialConstant]
  convert hr.2 using 1 <;> ring

end TheoremT.Continuum.WeakGrushin
