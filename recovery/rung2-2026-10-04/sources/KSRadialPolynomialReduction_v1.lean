import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

/-! Finite polynomial reduction by the actual radial equation r^2=sum X_i^2.
The output has degree at most one in r, given by explicit sums over the input
polynomial support and natural-number parity. No root selection, analytic
existence theorem or unspecified invariant decomposition is used. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

variable {R : Type*} [CommSemiring R]

def ksRadialSquare : MvPolynomial (Fin 3) R :=
  ∑ i : Fin 3, MvPolynomial.X i ^ 2

def ksRadialMonomialCore (d : Fin 4 →₀ ℕ) : MvPolynomial (Fin 3) R :=
  (∏ i : Fin 3, MvPolynomial.X i ^ d i.castSucc) *
    ksRadialSquare ^ (d (Fin.last 3) / 2)

def ksRadialEven (P : MvPolynomial (Fin 4) R) : MvPolynomial (Fin 3) R :=
  ∑ d ∈ P.support, MvPolynomial.C (P.coeff d) *
    if d (Fin.last 3) % 2 = 0 then ksRadialMonomialCore d else 0

def ksRadialOdd (P : MvPolynomial (Fin 4) R) : MvPolynomial (Fin 3) R :=
  ∑ d ∈ P.support, MvPolynomial.C (P.coeff d) *
    if d (Fin.last 3) % 2 = 0 then 0 else ksRadialMonomialCore d

theorem ks_radial_power_reduction (r q : R) (h : r^2=q) (k : ℕ) :
    r^k = q^(k/2) * if k%2=0 then 1 else r := by
  calc
    r^k = (r^2)^(k/2)*r^(k%2) := by
      rw [← pow_mul,← pow_add]
      congr 1
      omega
    _ = _ := by
      rw [h]
      by_cases hk : k%2=0
      · simp [hk]
      · have hk1 : k%2=1 := by omega
        simp [hk1]

theorem ksRadialMonomialCore_eval (X : Fin 3 → R) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.eval X (ksRadialMonomialCore d) =
      (∏ i : Fin 3, X i ^ d i.castSucc) * (∑ i : Fin 3, X i^2)^(d (Fin.last 3)/2) := by
  simp [ksRadialMonomialCore,ksRadialSquare,map_prod,map_sum]

theorem ks_radial_polynomial_reduction (P : MvPolynomial (Fin 4) R)
    (X : Fin 3 → R) (r : R) (h : r^2=∑ i : Fin 3, X i^2) :
    MvPolynomial.eval (Fin.snoc X r) P =
      MvPolynomial.eval X (ksRadialEven P) + r*MvPolynomial.eval X (ksRadialOdd P) := by
  rw [MvPolynomial.eval_eq']
  simp only [ksRadialEven,ksRadialOdd,map_sum,map_mul,MvPolynomial.eval_C,
    apply_ite,(MvPolynomial.eval X).map_zero,ksRadialMonomialCore_eval,
    Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc,Fin.snoc_last]
  rw [ks_radial_power_reduction r _ h]
  split_ifs <;> ring

end TheoremT.Continuum
