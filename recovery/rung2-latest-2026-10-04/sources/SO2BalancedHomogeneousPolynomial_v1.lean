import SO2ComplexPolynomialCoordinates_v1

/-! Balanced support in two independent variables determines every
homogeneous polynomial. Even degree gives one literal monomial; odd
degree gives zero, including polynomials with empty support. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

def so2BalancedExponent (m : ℕ) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 m + Finsupp.single 1 m

theorem so2_homogeneous_support_degree
    {P : MvPolynomial (Fin 2) ℂ} {k : ℕ} (hP : P.IsHomogeneous k)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ P.support) : d 0+d 1=k := by
  have hdeg : d.degree = k := by
    simpa only [Finsupp.degree_eq_weight_one,Pi.one_def] using hP (mem_support_iff.mp hd)
  simpa [Finsupp.degree_eq_sum,Fin.sum_univ_two] using hdeg

theorem so2_balanced_homogeneous_even (P : MvPolynomial (Fin 2) ℂ) (m : ℕ)
    (hP : P.IsHomogeneous (2*m))
    (hb : ∀ d ∈ P.support, d 0=d 1) :
    P = C (P.coeff (so2BalancedExponent m)) * (X 0*X 1)^m := by
  have heq : P=monomial (so2BalancedExponent m) (P.coeff (so2BalancedExponent m)) := by
    apply eq_monomial_of_support_subset_singleton
    intro d hd
    have hg := so2_homogeneous_support_degree hP hd
    have hb' := hb d hd
    have h0 : d 0=m := by omega
    have h1 : d 1=m := by omega
    ext i
    fin_cases i <;> simp [so2BalancedExponent,h0,h1]
  calc
    P = monomial (so2BalancedExponent m) (P.coeff (so2BalancedExponent m)) := heq
    _ = _ := by
      rw [mul_pow,← mul_assoc,C_mul_X_pow_eq_monomial,
        X_pow_eq_monomial,monomial_mul_monomial,mul_one]
      rfl

theorem so2_balanced_homogeneous_odd (P : MvPolynomial (Fin 2) ℂ) (m : ℕ)
    (hP : P.IsHomogeneous (2*m+1))
    (hb : ∀ d ∈ P.support, d 0=d 1) : P=0 := by
  apply MvPolynomial.ext
  intro d
  change P.coeff d = 0
  by_contra hc
  have hd : d ∈ P.support := mem_support_iff.mpr hc
  have hg := so2_homogeneous_support_degree hP hd
  have hb' := hb d hd
  omega

end TheoremT.Continuum
