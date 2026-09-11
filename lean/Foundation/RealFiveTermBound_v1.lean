import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace TheoremT.Continuum

theorem abs_sub_sub_add_sub_le (a b c d e : ℝ) :
    |a-b-c+d-e| ≤ |a|+|b|+|c|+|d|+|e| := by
  have h1 := abs_sub a b
  have h2 := abs_sub (a-b) c
  have h3 := abs_add_le (a-b-c) d
  have h4 := abs_sub (a-b-c+d) e
  linarith

theorem exp_weighted_five_term_bound (t a b c d e u v w : ℝ)
    (A B C D U V W : ℝ)
    (hA : |a*Real.exp t| ≤ A) (hB : |b*Real.exp t| ≤ B)
    (hC : |c*Real.exp t| ≤ C) (hD : |d*Real.exp t| ≤ D)
    (hU : |u| ≤ U) (hV : |v| ≤ V) (hW : |w| ≤ W)
    (he : e=d) :
    |Real.exp t*(a-b*v-c*u+d*(u*v-w))| ≤ A+B*V+C*U+D*U*V+D*W := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans hA
  have hB0 : 0 ≤ B := (abs_nonneg _).trans hB
  have hC0 : 0 ≤ C := (abs_nonneg _).trans hC
  have hD0 : 0 ≤ D := (abs_nonneg _).trans hD
  have hU0 : 0 ≤ U := (abs_nonneg _).trans hU
  have hV0 : 0 ≤ V := (abs_nonneg _).trans hV
  have hE : Real.exp t*(a-b*v-c*u+d*(u*v-w)) =
      a*Real.exp t-(b*Real.exp t)*v-(c*Real.exp t)*u+
        ((d*Real.exp t)*u)*v-(d*Real.exp t)*w := by ring
  rw [hE]
  apply (abs_sub_sub_add_sub_le _ _ _ _ _).trans
  simp only [abs_mul]
  have hb := mul_le_mul hB hV (abs_nonneg v) hB0
  have hc := mul_le_mul hC hU (abs_nonneg u) hC0
  have hd := mul_le_mul (mul_le_mul hD hU (abs_nonneg u) hD0) hV (abs_nonneg v)
    (mul_nonneg hD0 hU0)
  have hw := mul_le_mul hD hW (abs_nonneg w) hD0
  simp only [abs_mul] at hA hb hc hd hw
  linarith

#print axioms exp_weighted_five_term_bound
end TheoremT.Continuum
