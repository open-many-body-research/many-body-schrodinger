import SO2HomogeneousRadialDescent_v1

/-! Finite radial descent for every polynomial whose actual inverse complex
substitution has balanced support. The finite summation uses the image of
that literal support. Every radial coefficient is an original Cartesian
axis coefficient; no coefficient-norm amplification is introduced. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

theorem so2_balanced_exponent_eq {d e : Fin 2 →₀ ℕ}
    (hd : d 0=d 1) (he : e 0=e 1) (h0 : d 0=e 0) : d=e := by
  ext i
  fin_cases i
  · exact h0
  · change d 1=e 1
    omega

theorem so2PolynomialToCartesian_monomial (d : Fin 2 →₀ ℕ) (c : ℂ)
    (hd : d 0=d 1) :
    so2PolynomialToCartesian (monomial d c) = C c*so2RadialSquare^(d 0) := by
  have heq : monomial d c = C c*(X 0*X 1)^(d 0) := by
    rw [mul_pow,← mul_assoc,C_mul_X_pow_eq_monomial,
      X_pow_eq_monomial,monomial_mul_monomial,mul_one]
    have hd' : d=Finsupp.single 0 (d 0)+Finsupp.single 1 (d 0) := by
      ext i
      fin_cases i <;> simp [hd]
    rw [← hd']
  rw [heq,so2PolynomialToCartesian_balanced_power]

theorem so2PolynomialToCartesian_balanced_sum (P : MvPolynomial (Fin 2) ℂ)
    (hb : ∀ d ∈ P.support, d 0=d 1) :
    so2PolynomialToCartesian P = ∑ d ∈ P.support, C (P.coeff d)*so2RadialSquare^(d 0) := by
  conv_lhs => rw [← support_sum_monomial_coeff P]
  simp only [so2PolynomialToCartesian,eval₂_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact so2PolynomialToCartesian_monomial d (P.coeff d) (hb d hd)

theorem so2PolynomialToCartesian_balanced_axis_coeff
    (P : MvPolynomial (Fin 2) ℂ) (hb : ∀ d ∈ P.support, d 0=d 1)
    {d : Fin 2 →₀ ℕ} (hd : d ∈ P.support) :
    (so2PolynomialToCartesian P).coeff (Finsupp.single 0 (2*d 0)) = P.coeff d := by
  rw [so2PolynomialToCartesian_balanced_sum P hb]
  simp only [coeff_sum,so2RadialSquare_C_mul_coeff_axis]
  rw [Finset.sum_eq_single_of_mem d hd]
  · simp
  · intro e he hne
    have hdiff : 2*d 0 ≠ 2*e 0 := by
      intro h
      have heq : e=d := so2_balanced_exponent_eq (hb e he) (hb d hd) (by omega)
      exact hne heq
    simp [hdiff]

theorem so2_finite_radial_descent (P : MvPolynomial (Fin 2) ℂ)
    (hb : ∀ d ∈ (so2PolynomialToBalanced P).support, d 0=d 1) :
    P = ∑ m ∈ (so2PolynomialToBalanced P).support.image (fun d => d 0),
      C (P.coeff (Finsupp.single 0 (2*m)))*so2RadialSquare^m := by
  have hc (d : Fin 2 →₀ ℕ) (hd : d ∈ (so2PolynomialToBalanced P).support) :
      P.coeff (Finsupp.single 0 (2*d 0)) = (so2PolynomialToBalanced P).coeff d := by
    simpa only [so2PolynomialToCartesian_toBalanced] using
      so2PolynomialToCartesian_balanced_axis_coeff (so2PolynomialToBalanced P) hb hd
  rw [Finset.sum_image]
  · calc
      P = so2PolynomialToCartesian (so2PolynomialToBalanced P) :=
        (so2PolynomialToCartesian_toBalanced P).symm
      _ = _ := by
        rw [so2PolynomialToCartesian_balanced_sum (so2PolynomialToBalanced P) hb]
        apply Finset.sum_congr rfl
        intro d hd
        rw [hc d hd]
  · intro d hd e he h
    exact so2_balanced_exponent_eq (hb d hd) (hb e he) h

end TheoremT.Continuum
