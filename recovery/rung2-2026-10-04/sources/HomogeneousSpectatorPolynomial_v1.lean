import MvPolynomialCoefficientL1Substitution_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Embed one actual homogeneous polynomial and one spectator monomial into
independent coordinate blocks. The variable type sigma may be Fin 3 for KS
descent. This is a finite term construction, not a joint series theorem. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum
variable {σ τ : Type*} {d : ℕ}

theorem polynomialCoeffL1_rename_le (P : MvPolynomial σ ℂ) (f : σ → τ) :
    polynomialCoeffL1 (MvPolynomial.rename f P) ≤ polynomialCoeffL1 P := by
  simpa only [MvPolynomial.rename_eq_aeval, MvPolynomial.aeval_def,
    MvPolynomial.algebraMap_eq] using polynomialCoeffL1_substitution_nonexpansive
      P (MvPolynomial.X ∘ f) (fun i => by simp only [Function.comp_apply, polynomialCoeffL1_X, le_refl])

def homogeneousSpectatorPolynomial (P : MvPolynomial σ ℂ) (γ : Fin d → ℕ) :
    MvPolynomial (σ ⊕ Fin d) ℂ :=
  MvPolynomial.rename Sum.inl P *
    MvPolynomial.rename Sum.inr
      (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm γ) (1 : ℂ))

theorem homogeneousSpectatorPolynomial_eval
    (P : MvPolynomial σ ℂ) (γ : Fin d → ℕ) (X : σ → ℂ) (s : Fin d → ℂ) :
    MvPolynomial.eval (Sum.elim X s) (homogeneousSpectatorPolynomial P γ) =
      MvPolynomial.eval X P * ∏ i : Fin d, s i ^ γ i := by
  rw [homogeneousSpectatorPolynomial, map_mul, MvPolynomial.eval_rename,
    MvPolynomial.eval_rename]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, MvPolynomial.eval_monomial,
    one_mul]
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
  simp

theorem homogeneousSpectatorPolynomial_isHomogeneous
    {P : MvPolynomial σ ℂ} {m : ℕ} (hP : P.IsHomogeneous m) (γ : Fin d → ℕ) :
    (homogeneousSpectatorPolynomial P γ).IsHomogeneous (m + ∑ i : Fin d, γ i) := by
  apply hP.rename_isHomogeneous.mul
  apply MvPolynomial.IsHomogeneous.rename_isHomogeneous
  apply MvPolynomial.isHomogeneous_monomial
  simp [Finsupp.degree_eq_sum]

theorem polynomialCoeffL1_homogeneousSpectatorPolynomial
    (P : MvPolynomial σ ℂ) (γ : Fin d → ℕ) :
    polynomialCoeffL1 (homogeneousSpectatorPolynomial P γ) ≤ polynomialCoeffL1 P := by
  unfold homogeneousSpectatorPolynomial
  apply (polynomialCoeffL1_mul _ _).trans
  have hmon : polynomialCoeffL1 (MvPolynomial.rename (Sum.inr : Fin d → σ ⊕ Fin d)
      (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm γ) (1 : ℂ))) ≤ 1 := by
    simpa only [polynomialCoeffL1_monomial, norm_one] using
      polynomialCoeffL1_rename_le
        (MvPolynomial.monomial (Finsupp.equivFunOnFinite.symm γ) (1 : ℂ))
        (Sum.inr : Fin d → σ ⊕ Fin d)
  calc
    _ ≤ polynomialCoeffL1 P * 1 := mul_le_mul (polynomialCoeffL1_rename_le P Sum.inl)
      hmon (polynomialCoeffL1_nonneg _) (polynomialCoeffL1_nonneg _)
    _ = _ := mul_one _

end TheoremT.Continuum
