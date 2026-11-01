import SO2PolynomialRealRotation_v1
import SO2FiniteRadialDescent_v1

/-! Actual real planar rotation invariance implies exact radial polynomial
descent. These wrappers discharge the balanced-support premise; they do
not assume physical rotation invariance of an eigenfunction or its jets. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

theorem so2_finite_radial_descent_of_real_rotation
    (P : MvPolynomial (Fin 2) ℂ)
    (hrot : ∀ a b : ℝ, a^2+b^2=1 → ∀ x : Fin 2 → ℝ,
      eval (fun i => (so2RealRotation a b x i : ℂ)) P = eval (fun i => (x i : ℂ)) P) :
    P = ∑ m ∈ (so2PolynomialToBalanced P).support.image (fun d => d 0),
      C (P.coeff (Finsupp.single 0 (2*m)))*so2RadialSquare^m :=
  so2_finite_radial_descent P (so2PolynomialToBalanced_balanced_support_of_real_rotation P hrot)

theorem so2_homogeneous_even_radial_descent_of_real_rotation
    (P : MvPolynomial (Fin 2) ℂ) (m : ℕ) (hP : P.IsHomogeneous (2*m))
    (hrot : ∀ a b : ℝ, a^2+b^2=1 → ∀ x : Fin 2 → ℝ,
      eval (fun i => (so2RealRotation a b x i : ℂ)) P = eval (fun i => (x i : ℂ)) P) :
    P = C (P.coeff (Finsupp.single 0 (2*m)))*so2RadialSquare^m :=
  so2_homogeneous_even_radial_descent P m hP
    (so2PolynomialToBalanced_balanced_support_of_real_rotation P hrot)

theorem so2_homogeneous_odd_eq_zero_of_real_rotation
    (P : MvPolynomial (Fin 2) ℂ) (m : ℕ) (hP : P.IsHomogeneous (2*m+1))
    (hrot : ∀ a b : ℝ, a^2+b^2=1 → ∀ x : Fin 2 → ℝ,
      eval (fun i => (so2RealRotation a b x i : ℂ)) P = eval (fun i => (x i : ℂ)) P) : P=0 :=
  so2_homogeneous_odd_eq_zero P m hP
    (so2PolynomialToBalanced_balanced_support_of_real_rotation P hrot)

theorem so2_finite_radial_descent_of_local_real_rotation
    (P : MvPolynomial (Fin 2) ℂ) {r : ℝ} (hr : 0<r)
    (hrot : ∀ a b : ℝ, a^2+b^2=1 → ∀ x : Fin 2 → ℝ, (∀ i, |x i|<r) →
      eval (fun i => (so2RealRotation a b x i : ℂ)) P = eval (fun i => (x i : ℂ)) P) :
    P = ∑ m ∈ (so2PolynomialToBalanced P).support.image (fun d => d 0),
      C (P.coeff (Finsupp.single 0 (2*m)))*so2RadialSquare^m :=
  so2_finite_radial_descent P
    (so2PolynomialToBalanced_balanced_support_of_local_real_rotation P hr hrot)

end TheoremT.Continuum
