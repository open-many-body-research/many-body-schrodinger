import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-! Exact axis coefficients of the literal two-dimensional radial polynomial.
These are algebraic identities, with no assumption of rotational invariance. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum

def so2RadialSquare : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1 ^ 2

theorem so2RadialSquare_coeff_axis (m k : ℕ) :
    (so2RadialSquare ^ m).coeff (Finsupp.single 0 k) =
      if k = 2 * m then 1 else 0 := by
  let f : Fin 1 → Fin 2 := fun _ => 0
  have hf : Function.Injective f := fun _ _ _ => Subsingleton.elim _ _
  have hzero : MvPolynomial.killCompl hf (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) =
      (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ) := by
    simpa only [MvPolynomial.rename_X, f] using
      MvPolynomial.killCompl_rename_app hf (MvPolynomial.X (0 : Fin 1) : MvPolynomial (Fin 1) ℂ)
  have hone : MvPolynomial.killCompl hf (MvPolynomial.X 1 : MvPolynomial (Fin 2) ℂ) = 0 := by
    simp [MvPolynomial.killCompl, f]
  have hrestrict : MvPolynomial.killCompl hf (so2RadialSquare ^ m) =
      (MvPolynomial.X 0 : MvPolynomial (Fin 1) ℂ) ^ (2 * m) := by
    simp only [map_pow, so2RadialSquare, map_add, hzero, hone, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, add_zero, pow_mul]
  have hc := MvPolynomial.coeff_killCompl (p := so2RadialSquare ^ m)
    (s := Finsupp.single (0 : Fin 1) k) hf
  rw [hrestrict, Finsupp.mapDomain_single] at hc
  rw [← hc]
  simp [MvPolynomial.coeff_X_pow, eq_comm]

theorem so2RadialSquare_C_mul_coeff_axis (c : ℂ) (m k : ℕ) :
    (MvPolynomial.C c * so2RadialSquare ^ m).coeff (Finsupp.single 0 k) =
      if k = 2 * m then c else 0 := by
  rw [MvPolynomial.coeff_C_mul, so2RadialSquare_coeff_axis]
  split_ifs <;> simp

theorem so2RadialSquare_C_mul_coeff (c : ℂ) (m : ℕ) :
    (MvPolynomial.C c * so2RadialSquare ^ m).coeff (Finsupp.single 0 (2 * m)) = c := by
  rw [so2RadialSquare_C_mul_coeff_axis, if_pos rfl]

end TheoremT.Continuum
