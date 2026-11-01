import SO2BalancedHomogeneousPolynomial_v1
import SO2RadialPolynomialCoefficient_v1

/-! Exact homogeneous SO(2) descent with an explicit balanced-support
premise after the literal inverse complex substitution. The resulting
radial coefficient is an original Cartesian coefficient, with no norm
conversion factor. Deriving balance from physical invariance is separate. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
open MvPolynomial

theorem so2ForwardPolynomial_mul :
    so2ForwardPolynomial 0 * so2ForwardPolynomial 1 = so2RadialSquare := by
  apply MvPolynomial.funext
  intro z
  simp [so2ForwardPolynomial,so2RadialSquare]
  ring_nf
  norm_num [Complex.I_sq]

theorem so2PolynomialToCartesian_balanced_power (c : ℂ) (m : ℕ) :
    so2PolynomialToCartesian (C c*(X 0*X 1)^m) = C c*so2RadialSquare^m := by
  simp [so2PolynomialToCartesian,so2ForwardPolynomial_mul]

theorem so2_homogeneous_even_radial_descent
    (P : MvPolynomial (Fin 2) ℂ) (m : ℕ) (hP : P.IsHomogeneous (2*m))
    (hb : ∀ d ∈ (so2PolynomialToBalanced P).support, d 0=d 1) :
    P = C (P.coeff (Finsupp.single 0 (2*m))) * so2RadialSquare^m := by
  let c := (so2PolynomialToBalanced P).coeff (so2BalancedExponent m)
  have hraw : P=C c*so2RadialSquare^m := by
    calc
      P = so2PolynomialToCartesian (so2PolynomialToBalanced P) :=
        (so2PolynomialToCartesian_toBalanced P).symm
      _ = _ := by
        rw [so2_balanced_homogeneous_even (so2PolynomialToBalanced P) m
          (so2PolynomialToBalanced_homogeneous hP) hb]
        exact so2PolynomialToCartesian_balanced_power c m
  have hc := congrArg (fun Q : MvPolynomial (Fin 2) ℂ =>
    Q.coeff (Finsupp.single 0 (2*m))) hraw
  rw [so2RadialSquare_C_mul_coeff] at hc
  calc
    P = C c*so2RadialSquare^m := hraw
    _ = _ := by rw [hc]

theorem so2_homogeneous_odd_eq_zero
    (P : MvPolynomial (Fin 2) ℂ) (m : ℕ) (hP : P.IsHomogeneous (2*m+1))
    (hb : ∀ d ∈ (so2PolynomialToBalanced P).support, d 0=d 1) : P=0 := by
  have hzero := so2_balanced_homogeneous_odd (so2PolynomialToBalanced P) m
    (so2PolynomialToBalanced_homogeneous hP) hb
  calc
    P = so2PolynomialToCartesian (so2PolynomialToBalanced P) :=
      (so2PolynomialToCartesian_toBalanced P).symm
    _ = 0 := by rw [hzero]; simp [so2PolynomialToCartesian]

end TheoremT.Continuum
