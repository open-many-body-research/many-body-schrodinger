import KSSpinorPolynomialRealSlice_v1

/-! Odd homogeneous degree cannot occur in a balanced spinor polynomial.
The literal inverse spinor substitution is injective, so this vanishing
also holds for the original four real-coordinate polynomial. The degree
here concerns the four KS variables only, without spectator variables. -/
set_option autoImplicit false
noncomputable section
namespace TheoremT.Continuum
open MvPolynomial

theorem ksBalancedPolynomial_odd_eq_zero
    {P : MvPolynomial (Fin 4) ℂ} {m : ℕ}
    (hP : P.IsHomogeneous (2*m+1))
    (hbalanced : ∀ d ∈ P.support, d 0+d 1=d 2+d 3) : P=0 := by
  ext d
  change P.coeff d=0
  by_contra hd
  have hb := hbalanced d (mem_support_iff.mpr hd)
  have he : d.degree=2*m+1 := by
    by_contra hn
    exact hd (hP.coeff_eq_zero hn)
  have hsum : d.degree=d 0+d 1+d 2+d 3 := by
    simp [Finsupp.degree_eq_sum,Fin.sum_univ_succ]
    omega
  omega

theorem ksRealPolynomialToSpinor_injective :
    Function.Injective ksRealPolynomialToSpinor := by
  intro P Q h
  apply complexPolynomial_eq_of_real_eval_eq
  intro x
  let y : KSSpace := WithLp.toLp 2 x
  change eval (fun i => (y i : ℂ)) P = eval (fun i => (y i : ℂ)) Q
  rw [← ksRealPolynomialToSpinor_physical_eval P y,
    ← ksRealPolynomialToSpinor_physical_eval Q y,h]

theorem ksRealPolynomial_odd_eq_zero_of_balanced
    {P : MvPolynomial (Fin 4) ℂ} {m : ℕ}
    (hP : P.IsHomogeneous (2*m+1))
    (hbalanced : ∀ d ∈ (ksRealPolynomialToSpinor P).support,
      d 0+d 1=d 2+d 3) : P=0 := by
  apply ksRealPolynomialToSpinor_injective
  have hz := ksBalancedPolynomial_odd_eq_zero
    (ksRealPolynomialToSpinor_homogeneous hP) hbalanced
  simpa only [ksRealPolynomialToSpinor,eval₂_zero] using hz

end TheoremT.Continuum
