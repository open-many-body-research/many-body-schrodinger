import CoulombKSPhysicalFactorial_v1

/-! Monotonic enlargement of the actual physical KS source and H12 budgets.
The proof retains the identical weak derivative family and all its identities;
only the upper bound on its already finite weighted profile is enlarged. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open WeakGrushin

theorem commonKSBoxFactorialConstant_one_le (M : ℝ) :
    1 ≤ commonKSBoxFactorialConstant M :=
  (fixedBoxFactorialConstant_one_le 1 M).trans (le_max_left _ _)

theorem PhysicalKSBoxFactorialData.mono_source_budget
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 F1 W0 W1 : ℝ}
    (h : PhysicalKSBoxFactorialData f t0 M A F0 W0)
    (_hM : 1 ≤ M) (hA : 1 ≤ A) (hF0 : 0 ≤ F0) (hW0 : 0 ≤ W0)
    (hF : F0 ≤ F1) (hW : W0 ≤ W1) :
    PhysicalKSBoxFactorialData f t0 M A F1 W1 := by
  obtain ⟨F,h0,hreg,hY,hT,hbound⟩ := h
  refine ⟨F,h0,hreg,hY,hT,?_⟩
  intro r
  refine ⟨(hbound r).1,((hbound r).2).trans ?_⟩
  have hC : 0 ≤ commonKSBoxFactorialConstant M :=
    zero_le_one.trans (commonKSBoxFactorialConstant_one_le M)
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  gcongr

end TheoremT.Continuum
