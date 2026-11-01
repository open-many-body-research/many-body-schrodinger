import MvPolynomialCoefficientL1Substitution_v1

/-! Exact absolute homogeneity of the literal coefficient L1 norm. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ : Type*}

theorem polynomialCoeffL1_C_mul (c : ℂ) (p : MvPolynomial σ ℂ) :
    polynomialCoeffL1 (MvPolynomial.C c*p) = ‖c‖*polynomialCoeffL1 p := by
  classical
  have hs : (MvPolynomial.C c*p).support ⊆ p.support := by
    intro d hd
    by_contra hn
    have hz : (MvPolynomial.C c*p).coeff d = 0 := by
      rw [MvPolynomial.coeff_C_mul,MvPolynomial.notMem_support_iff.mp hn,mul_zero]
    exact (MvPolynomial.mem_support_iff.mp hd) hz
  rw [polynomialCoeffL1_eq_sum_of_support_subset _ _ hs,polynomialCoeffL1_eq_sum,Finset.mul_sum]
  exact Finset.sum_congr rfl (fun d _ => by rw [MvPolynomial.coeff_C_mul,norm_mul])

theorem polynomialCoeffL1_smul (c : ℂ) (p : MvPolynomial σ ℂ) :
    polynomialCoeffL1 (c • p) = ‖c‖*polynomialCoeffL1 p := by
  rw [← MvPolynomial.C_mul',polynomialCoeffL1_C_mul]

theorem polynomialCoeffL1_neg (p : MvPolynomial σ ℂ) : polynomialCoeffL1 (-p) = polynomialCoeffL1 p := by
  have h := polynomialCoeffL1_smul (-1 : ℂ) p
  simpa only [neg_one_smul,norm_neg,norm_one,one_mul] using h

end TheoremT.Continuum
