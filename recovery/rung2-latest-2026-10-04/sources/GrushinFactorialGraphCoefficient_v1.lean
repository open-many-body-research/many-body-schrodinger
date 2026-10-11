import GrushinFactorialMonomialBound_v1

/-! Explicit scalar coefficient used in the compact weighted graph bound. -/
noncomputable section
namespace TheoremT.Continuum.WeakGrushin

def factorialGraphCoefficient (R c : ℝ) : ℝ := 4*R^2+2*R+2+2/c

theorem factorialGraphCoefficient_bounds {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    4*R^2 ≤ factorialGraphCoefficient R c ∧
    2*R ≤ factorialGraphCoefficient R c ∧
    2 ≤ factorialGraphCoefficient R c ∧
    2 ≤ c*factorialGraphCoefficient R c := by
  have hdiv : 0 ≤ 2/c := by positivity
  have he : c*factorialGraphCoefficient R c = c*(4*R^2+2*R+2)+2 := by
    unfold factorialGraphCoefficient
    field_simp
    <;> ring
  refine ⟨?_,?_,?_,?_⟩
  · unfold factorialGraphCoefficient
    nlinarith [sq_nonneg R]
  · unfold factorialGraphCoefficient
    nlinarith [sq_nonneg R]
  · unfold factorialGraphCoefficient
    nlinarith [sq_nonneg R]
  · rw [he]
    have hp : 0 ≤ c*(4*R^2+2*R+2) := by positivity
    linarith

theorem positive_weighted_square_bound {a b C E I : ℝ}
    (ha : 0 < a) (hE : 0 ≤ E) (hC : b ≤ a*C^2) (hI : a*I ≤ b*E) :
    I ≤ C^2*E := by
  apply (mul_le_mul_iff_right₀ ha).mp
  calc
    a*I ≤ b*E := hI
    _ ≤ (a*C^2)*E := mul_le_mul_of_nonneg_right hC hE
    _ = _ := by ring

end TheoremT.Continuum.WeakGrushin
