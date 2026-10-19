import KSRadialPolynomialReduction_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Exact degrees after radial reduction. A degree-m polynomial in X,r
reduces to A of degree m and B of degree m-1 in X. The zero-degree case is
handled separately: its odd output is identically zero. Thus no degree-m
bound is silently applied to the degree-(m-1) radial coefficient. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
variable {R : Type*} [CommSemiring R]

theorem ksRadialSquare_isHomogeneous :
    (ksRadialSquare : MvPolynomial (Fin 3) R).IsHomogeneous 2 := by
  apply MvPolynomial.IsHomogeneous.sum
  intro i hi
  exact MvPolynomial.isHomogeneous_X_pow i 2

theorem ksRadialMonomialCore_isHomogeneous (d : Fin 4 →₀ ℕ) :
    (ksRadialMonomialCore d : MvPolynomial (Fin 3) R).IsHomogeneous
      ((∑ i : Fin 3, d i.castSucc) + 2*(d (Fin.last 3)/2)) := by
  exact (MvPolynomial.IsHomogeneous.prod Finset.univ
    (fun i : Fin 3 => MvPolynomial.X i ^ d i.castSucc)
    (fun i : Fin 3 => d i.castSucc)
    (fun i hi => MvPolynomial.isHomogeneous_X_pow i _)).mul
      (ksRadialSquare_isHomogeneous.pow _)

theorem ks_radial_support_degree {P : MvPolynomial (Fin 4) R} {m : ℕ}
    (hP : P.IsHomogeneous m) {d : Fin 4 →₀ ℕ} (hd : d ∈ P.support) :
    (∑ i : Fin 3, d i.castSucc) + d (Fin.last 3) = m := by
  have he : d.degree=m := by
    by_contra hn
    exact (MvPolynomial.mem_support_iff.mp hd) (hP.coeff_eq_zero hn)
  simpa only [Finsupp.degree_eq_sum,Fin.sum_univ_castSucc] using he

theorem ksRadialEven_isHomogeneous {P : MvPolynomial (Fin 4) R} {m : ℕ}
    (hP : P.IsHomogeneous m) : (ksRadialEven P).IsHomogeneous m := by
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  by_cases hp : d (Fin.last 3)%2=0
  · simp only [if_pos hp]
    have he := ks_radial_support_degree hP hd
    have hm : (∑ i : Fin 3, d i.castSucc)+2*(d (Fin.last 3)/2)=m := by omega
    rw [← hm]
    exact (ksRadialMonomialCore_isHomogeneous d).C_mul _
  · simp only [if_neg hp,mul_zero]
    exact MvPolynomial.isHomogeneous_zero (Fin 3) R _

theorem ksRadialOdd_isHomogeneous {P : MvPolynomial (Fin 4) R} {m : ℕ}
    (hP : P.IsHomogeneous m) : (ksRadialOdd P).IsHomogeneous (m-1) := by
  apply MvPolynomial.IsHomogeneous.sum
  intro d hd
  by_cases hp : d (Fin.last 3)%2=0
  · simp only [if_pos hp,mul_zero]
    exact MvPolynomial.isHomogeneous_zero (Fin 3) R _
  · simp only [if_neg hp]
    have he := ks_radial_support_degree hP hd
    have hm : (∑ i : Fin 3, d i.castSucc)+2*(d (Fin.last 3)/2)=m-1 := by omega
    rw [← hm]
    exact (ksRadialMonomialCore_isHomogeneous d).C_mul _

theorem ksRadialOdd_eq_zero_of_degree_zero {P : MvPolynomial (Fin 4) R}
    (hP : P.IsHomogeneous 0) : ksRadialOdd P=0 := by
  apply Finset.sum_eq_zero
  intro d hd
  have he := ks_radial_support_degree hP hd
  have hz : d (Fin.last 3)=0 := by omega
  rw [hz]
  simp

end TheoremT.Continuum
