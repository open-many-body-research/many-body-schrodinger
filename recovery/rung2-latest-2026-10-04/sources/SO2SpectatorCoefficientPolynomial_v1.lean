import MvPolynomialSumCoefficient_v1
import MvPolynomialCoefficientL1Substitution_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Adapted from the immutable KSSpectatorCoefficientPolynomial_v1.
Literal spectator coefficient extraction from a joint two-plus-two
variable polynomial. Spectator exponents index the outer polynomial and
its coefficients are genuine two-variable polynomials. All original
complex coefficients are retained exactly. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

def so2SpectatorPolynomial (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) :
    MvPolynomial (Fin 2) (MvPolynomial (Fin 2) ℂ) :=
  sumRingEquiv ℂ (Fin 2) (Fin 2) (rename Sum.swap P)

def so2SpectatorCoefficientPolynomial (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ)
    (γ : Fin 2 →₀ ℕ) : MvPolynomial (Fin 2) ℂ :=
  (so2SpectatorPolynomial P).coeff γ

theorem so2SpectatorCoefficientPolynomial_coeff
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (γ : Fin 2 →₀ ℕ) (α : Fin 2 →₀ ℕ) :
    (so2SpectatorCoefficientPolynomial P γ).coeff α = P.coeff (Finsupp.sumElim α γ) := by
  unfold so2SpectatorCoefficientPolynomial so2SpectatorPolynomial
  rw [mvPolynomial_sumRingEquiv_coeff_coeff]
  rw [← Finsupp.mapDomain_swap_sumElim α γ]
  exact coeff_rename_mapDomain Sum.swap (Equiv.sumComm (Fin 2) (Fin 2)).injective P (Finsupp.sumElim α γ)

theorem so2SpectatorPolynomial_eval
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (y : Fin 2 → ℂ) (t : Fin 2 → ℂ) :
    eval₂ (eval y) t (so2SpectatorPolynomial P) = eval (Sum.elim y t) P := by
  unfold so2SpectatorPolynomial
  rw [mvPolynomial_sumRingEquiv_eval,eval_rename]
  apply congrArg (fun f : Fin 2 ⊕ Fin 2 → ℂ => eval f P)
  funext i
  cases i <;> rfl

theorem so2SpectatorCoefficientPolynomial_eval_reconstruct
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (y : Fin 2 → ℂ) (t : Fin 2 → ℂ) :
    eval (Sum.elim y t) P =
      ∑ γ ∈ (so2SpectatorPolynomial P).support,
        eval y (so2SpectatorCoefficientPolynomial P γ) * ∏ i : Fin 2, t i ^ γ i := by
  rw [← so2SpectatorPolynomial_eval P y t,eval₂_eq']
  rfl

theorem so2JointMultiindex_degree (α : Fin 2 →₀ ℕ) (γ : Fin 2 →₀ ℕ) :
    (Finsupp.sumElim α γ).degree = α.degree + γ.degree := by
  simp [Finsupp.degree_eq_sum,Fintype.sum_sum_type,Finsupp.sumElim_apply]

theorem so2SpectatorCoefficientPolynomial_homogeneous
    {P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ} {n : ℕ} (hP : P.IsHomogeneous n)
    (γ : Fin 2 →₀ ℕ) :
    (so2SpectatorCoefficientPolynomial P γ).IsHomogeneous (n-γ.degree) := by
  intro α hα
  change Finsupp.weight (fun _ : Fin 2 => 1) α = n-γ.degree
  rw [← Finsupp.degree_eq_weight_one]
  have hne : P.coeff (Finsupp.sumElim α γ) ≠ 0 := by
    rwa [so2SpectatorCoefficientPolynomial_coeff] at hα
  have hh : (Finsupp.sumElim α γ).degree = n := by
    by_contra hn
    exact hne (hP.coeff_eq_zero hn)
  rw [so2JointMultiindex_degree] at hh
  omega

theorem so2SpectatorCoefficientPolynomial_eq_zero_of_degree_lt
    {P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ} {n : ℕ} (hP : P.IsHomogeneous n)
    (γ : Fin 2 →₀ ℕ) (hγ : n<γ.degree) : so2SpectatorCoefficientPolynomial P γ=0 := by
  ext α
  rw [so2SpectatorCoefficientPolynomial_coeff]
  change P.coeff (Finsupp.sumElim α γ) = 0
  apply hP.coeff_eq_zero
  rw [so2JointMultiindex_degree]
  omega

theorem polynomialCoeffL1_so2SpectatorCoefficientPolynomial
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (γ : Fin 2 →₀ ℕ) :
    polynomialCoeffL1 (so2SpectatorCoefficientPolynomial P γ) ≤ polynomialCoeffL1 P := by
  classical
  let f : (Fin 2 →₀ ℕ) → (Fin 2 ⊕ Fin 2 →₀ ℕ) := fun α => Finsupp.sumElim α γ
  have hf : Function.Injective f := by
    intro α β h
    ext i
    exact congrArg (fun d : Fin 2 ⊕ Fin 2 →₀ ℕ => d (Sum.inl i)) h
  have hs : (so2SpectatorCoefficientPolynomial P γ).support.image f ⊆ P.support := by
    intro d hd
    obtain ⟨α,hα,rfl⟩ := Finset.mem_image.mp hd
    apply mem_support_iff.mpr
    have hne := mem_support_iff.mp hα
    simpa only [so2SpectatorCoefficientPolynomial_coeff] using hne
  rw [polynomialCoeffL1_eq_sum,polynomialCoeffL1_eq_sum]
  calc
    _ = ∑ d ∈ (so2SpectatorCoefficientPolynomial P γ).support.image f, ‖P.coeff d‖ := by
      rw [Finset.sum_image (fun α _ β _ h => hf h)]
      exact Finset.sum_congr rfl (fun α _ => by rw [so2SpectatorCoefficientPolynomial_coeff])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => norm_nonneg _)

theorem so2SpectatorCoefficientPolynomial_coefficient_bound
    (P : MvPolynomial (Fin 2 ⊕ Fin 2) ℂ) (γ : Fin 2 →₀ ℕ) (α : Fin 2 →₀ ℕ) :
    ‖(so2SpectatorCoefficientPolynomial P γ).coeff α‖ ≤ polynomialCoeffL1 P := by
  rw [so2SpectatorCoefficientPolynomial_coeff]
  exact polynomialCoeffL1_coefficient_bound P (Finsupp.sumElim α γ)

end TheoremT.Continuum
