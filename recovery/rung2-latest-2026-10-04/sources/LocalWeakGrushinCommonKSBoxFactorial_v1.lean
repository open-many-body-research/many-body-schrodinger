import LocalWeakGrushinFixedBoxFactorial_v1

/-! One explicit local bound for the principal constants of all three
physical KS charts: c=1 for the pair chart and c=4 for nuclear charts.
The actual physical solution coupling remains a separate theorem. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin

def commonKSBoxFactorialConstant (M : ℝ) : ℝ :=
  max (fixedBoxFactorialConstant 1 M) (fixedBoxFactorialConstant 4 M)

theorem fixedBoxFactorialConstant_one_le (c M : ℝ) :
    1 ≤ fixedBoxFactorialConstant c M := le_max_left _ _

theorem fixedBoxFactorialConstant_le_common {c : ℝ}
    (hc : c = 1 ∨ c = 4) (M : ℝ) :
    fixedBoxFactorialConstant c M ≤ commonKSBoxFactorialConstant M := by
  rcases hc with rfl | rfl
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem local_weak_grushin_common_KS_box_factorial
    (t0 : Position) (c : ℝ) (hc : c = 1 ∨ c = 4)
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
        let C := commonKSBoxFactorialConstant M
        factorialLocalProfile F (rectangularOpenBox (0,t0) (1/256) (1/256)) r ≤
          12*C*A*(F0+498*Real.sqrt W)*(3072*C*A)^r*(r.factorial : ℝ) := by
  have hcpos : 0 < c := by rcases hc with rfl | rfl <;> norm_num
  obtain ⟨F,h0,hreg,hY,hT,hbound⟩ := local_weak_grushin_fixed_box_factorial t0 c hcpos
    hB hs hf hEq M A F0 hM hA hF0 hBb hSourceBudget W h12
  refine ⟨F,h0,hreg,hY,hT,?_⟩
  intro r
  refine ⟨(hbound r).1,?_⟩
  have hC0 := zero_le_one.trans (fixedBoxFactorialConstant_one_le c M)
  have hCK := fixedBoxFactorialConstant_le_common hc M
  have hK0 := hC0.trans hCK
  have hA0 := zero_le_one.trans hA
  have hS : 0 ≤ F0+498*Real.sqrt W := by positivity
  apply ((hbound r).2).trans
  gcongr <;> positivity

end TheoremT.Continuum.WeakGrushin
