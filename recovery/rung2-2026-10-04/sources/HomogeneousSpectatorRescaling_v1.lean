import HomogeneousSpectatorPolynomial_v1
import MvPolynomialCoefficientL1Scaling_v1

/-! Actual rescaling of homogeneous radial/spectator coefficient families.
This is a scalar multiplication of each specified polynomial, justified
by its exact homogeneity, and retains both anisotropic geometric rates. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*} {d : ℕ}

theorem homogeneous_polynomial_eval_scale
    (P : MvPolynomial σ ℂ) {m : ℕ} (hP : P.IsHomogeneous m)
    (a : ℂ) (X : σ → ℂ) :
    MvPolynomial.eval (fun i => a*X i) P = a^m * MvPolynomial.eval X P := by
  classical
  rw [MvPolynomial.eval_eq,MvPolynomial.eval_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  simp only [mul_pow,Finset.prod_mul_distrib]
  rw [Finset.prod_pow_eq_pow_sum,← hP.degree_eq_sum_deg_support he]
  ring

def rescaledHomogeneousSpectatorFamily
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ) (a b : ℝ)
    (m : ℕ) (γ : Fin d → ℕ) : MvPolynomial σ ℂ :=
  MvPolynomial.C ((a : ℂ)^m*(b : ℂ)^(∑ i : Fin d, γ i))*A m γ

theorem rescaledHomogeneousSpectatorFamily_isHomogeneous
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) (a b : ℝ) (m : ℕ) (γ : Fin d → ℕ) :
    (rescaledHomogeneousSpectatorFamily A a b m γ).IsHomogeneous m :=
  (hA m γ).C_mul _

theorem rescaledHomogeneousSpectatorFamily_eval
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m) (a b : ℝ) (m : ℕ) (γ : Fin d → ℕ)
    (X : σ → ℂ) (s : Fin d → ℂ) :
    MvPolynomial.eval X (rescaledHomogeneousSpectatorFamily A a b m γ)*∏ i : Fin d, s i^γ i =
      MvPolynomial.eval (fun i => (a : ℂ)*X i) (A m γ)*
        ∏ i : Fin d, ((b : ℂ)*s i)^γ i := by
  rw [rescaledHomogeneousSpectatorFamily,map_mul,MvPolynomial.eval_C,
    homogeneous_polynomial_eval_scale _ (hA m γ)]
  simp only [mul_pow,Finset.prod_mul_distrib,Finset.prod_pow_eq_pow_sum]
  ring

theorem polynomialCoeffL1_rescaledHomogeneousSpectatorFamily
    (A : ℕ → (Fin d → ℕ) → MvPolynomial σ ℂ) {M D S a b T : ℝ}
    (hM : 0 ≤ M) (hD : 0 ≤ D) (hS : 0 ≤ S) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hDT : D*a ≤ T) (hST : S*b ≤ T)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i))
    (m : ℕ) (γ : Fin d → ℕ) :
    polynomialCoeffL1 (rescaledHomogeneousSpectatorFamily A a b m γ) ≤
      M*T^(m+∑ i : Fin d, γ i) := by
  have hT : 0 ≤ T := (mul_nonneg hD ha).trans hDT
  rw [rescaledHomogeneousSpectatorFamily,polynomialCoeffL1_C_mul]
  simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg ha,abs_of_nonneg hb]
  calc
    _ ≤ (a^m*b^(∑ i : Fin d, γ i))*(M*D^m*S^(∑ i : Fin d, γ i)) := by gcongr; exact hL m γ
    _ = M*(D*a)^m*(S*b)^(∑ i : Fin d, γ i) := by rw [mul_pow,mul_pow]; ring
    _ ≤ M*T^m*T^(∑ i : Fin d, γ i) := by gcongr
    _ = _ := by rw [pow_add]; ring

end TheoremT.Continuum
