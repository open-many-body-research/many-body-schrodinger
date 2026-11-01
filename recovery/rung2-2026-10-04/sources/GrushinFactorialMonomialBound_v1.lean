import GrushinFactorialOuterL2_v1

/-! Actual spatial monomial bounds for the exact outer index set.  The
radial exponent is the minimum one required by R3; it is zero for u,Y,T,YY,
one for YT, and two for TT.  A spatial support radius at least one absorbs
the remaining polynomial degree without any lower bound on |y|. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

def factorialOuterRadialOrder (α : Fin 4 → ℕ) (β : Fin 3 → ℕ) : ℕ :=
  (∑ i, α i)+2*(∑ j, β j)-2

theorem factorialYMonomial_continuous (γ : Fin 4 → ℕ) :
    Continuous (factorialYMonomial γ) := by
  unfold factorialYMonomial
  exact continuous_finsetProd _ (fun i _ => (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) i).pow _)

theorem factorialYMonomial_abs_le (γ : Fin 4 → ℕ)
    (y : EuclideanSpace ℝ (Fin 4)) :
    |factorialYMonomial γ y| ≤ ‖y‖^(∑ i, γ i) := by
  unfold factorialYMonomial
  rw [Finset.abs_prod]
  simp_rw [abs_pow]
  calc
    (∏ i, |y i|^(γ i)) ≤ ∏ i, ‖y‖^(γ i) := by
      apply Finset.prod_le_prod₀ (fun i _ => by positivity)
      intro i hi
      exact pow_le_pow_left₀ (abs_nonneg _) (by
        simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le y i) _
    _ = _ := Finset.prod_pow_eq_pow_sum _ _ _

theorem factorialYMonomial_radial_bound (γ : Fin 4 → ℕ) (q : ℕ)
    (hq : q ≤ ∑ i, γ i) (hγ : (∑ i, γ i) ≤ 2)
    (R : ℝ) (hR : 1 ≤ R) (y : EuclideanSpace ℝ (Fin 4)) (hy : ‖y‖ ≤ R) :
    |factorialYMonomial γ y| ≤ R^2*‖y‖^q := by
  have hrem : (∑ i, γ i)-q ≤ 2 := by omega
  have hp : ‖y‖^((∑ i, γ i)-q) ≤ R^2 :=
    (pow_le_pow_left₀ (norm_nonneg _) hy _).trans (pow_le_pow_right₀ hR hrem)
  calc
    |factorialYMonomial γ y| ≤ ‖y‖^(∑ i, γ i) := factorialYMonomial_abs_le γ y
    _ = ‖y‖^((∑ i, γ i)-q)*‖y‖^q := by
      rw [← pow_add,Nat.sub_add_cancel hq]
    _ ≤ R^2*‖y‖^q := mul_le_mul_of_nonneg_right hp (by positivity)

theorem factorialOuterRadialOrder_le {m : FactorialOuterIndex}
    (hm : m ∈ factorialOuterIndices) :
    factorialOuterRadialOrder m.1 m.2.1 ≤ ∑ i, m.2.2 i := by
  have h := (factorialOuterIndices_mem m).mp hm
  unfold factorialOuterRadialOrder factorialOuterAdmissible at *
  omega

theorem factorial_outer_monomial_bound {m : FactorialOuterIndex}
    (hm : m ∈ factorialOuterIndices) (R : ℝ) (hR : 1 ≤ R)
    (y : EuclideanSpace ℝ (Fin 4)) (hy : ‖y‖ ≤ R) :
    |factorialYMonomial m.2.2 y| ≤ R^2*‖y‖^(factorialOuterRadialOrder m.1 m.2.1) :=
  factorialYMonomial_radial_bound _ _ (factorialOuterRadialOrder_le hm)
    ((factorialOuterIndices_mem m).mp hm).2.1 R hR y hy

end TheoremT.Continuum.WeakGrushin
