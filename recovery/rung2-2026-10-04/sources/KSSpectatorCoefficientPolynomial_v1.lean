import MvPolynomialSumCoefficient_v1
import MvPolynomialCoefficientL1Substitution_v1
import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! Literal spectator coefficient extraction from a joint four-plus-three
variable polynomial. Spectator exponents index the outer polynomial and
its coefficients are genuine four-variable polynomials. All original
complex coefficients are retained exactly. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum
open MvPolynomial

def ksSpectatorPolynomial (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) :
    MvPolynomial (Fin 3) (MvPolynomial (Fin 4) ℂ) :=
  sumRingEquiv ℂ (Fin 3) (Fin 4) (rename Sum.swap P)

def ksSpectatorCoefficientPolynomial (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ)
    (γ : Fin 3 →₀ ℕ) : MvPolynomial (Fin 4) ℂ :=
  (ksSpectatorPolynomial P).coeff γ

theorem ksSpectatorCoefficientPolynomial_coeff
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (γ : Fin 3 →₀ ℕ) (α : Fin 4 →₀ ℕ) :
    (ksSpectatorCoefficientPolynomial P γ).coeff α = P.coeff (Finsupp.sumElim α γ) := by
  unfold ksSpectatorCoefficientPolynomial ksSpectatorPolynomial
  rw [mvPolynomial_sumRingEquiv_coeff_coeff]
  rw [← Finsupp.mapDomain_swap_sumElim α γ]
  exact coeff_rename_mapDomain Sum.swap (Equiv.sumComm (Fin 4) (Fin 3)).injective P (Finsupp.sumElim α γ)

theorem ksSpectatorPolynomial_eval
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (y : Fin 4 → ℂ) (t : Fin 3 → ℂ) :
    eval₂ (eval y) t (ksSpectatorPolynomial P) = eval (Sum.elim y t) P := by
  unfold ksSpectatorPolynomial
  rw [mvPolynomial_sumRingEquiv_eval,eval_rename]
  apply congrArg (fun f : Fin 4 ⊕ Fin 3 → ℂ => eval f P)
  funext i
  cases i <;> rfl

theorem ksSpectatorCoefficientPolynomial_eval_reconstruct
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (y : Fin 4 → ℂ) (t : Fin 3 → ℂ) :
    eval (Sum.elim y t) P =
      ∑ γ ∈ (ksSpectatorPolynomial P).support,
        eval y (ksSpectatorCoefficientPolynomial P γ) * ∏ i : Fin 3, t i ^ γ i := by
  rw [← ksSpectatorPolynomial_eval P y t,eval₂_eq']
  rfl

theorem ksJointMultiindex_degree (α : Fin 4 →₀ ℕ) (γ : Fin 3 →₀ ℕ) :
    (Finsupp.sumElim α γ).degree = α.degree + γ.degree := by
  simp [Finsupp.degree_eq_sum,Fintype.sum_sum_type,Finsupp.sumElim_apply]

theorem ksSpectatorCoefficientPolynomial_homogeneous
    {P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ} {n : ℕ} (hP : P.IsHomogeneous n)
    (γ : Fin 3 →₀ ℕ) :
    (ksSpectatorCoefficientPolynomial P γ).IsHomogeneous (n-γ.degree) := by
  intro α hα
  change Finsupp.weight (fun _ : Fin 4 => 1) α = n-γ.degree
  rw [← Finsupp.degree_eq_weight_one]
  have hne : P.coeff (Finsupp.sumElim α γ) ≠ 0 := by
    rwa [ksSpectatorCoefficientPolynomial_coeff] at hα
  have hh : (Finsupp.sumElim α γ).degree = n := by
    by_contra hn
    exact hne (hP.coeff_eq_zero hn)
  rw [ksJointMultiindex_degree] at hh
  omega

theorem ksSpectatorCoefficientPolynomial_eq_zero_of_degree_lt
    {P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ} {n : ℕ} (hP : P.IsHomogeneous n)
    (γ : Fin 3 →₀ ℕ) (hγ : n<γ.degree) : ksSpectatorCoefficientPolynomial P γ=0 := by
  ext α
  rw [ksSpectatorCoefficientPolynomial_coeff]
  change P.coeff (Finsupp.sumElim α γ) = 0
  apply hP.coeff_eq_zero
  rw [ksJointMultiindex_degree]
  omega

theorem polynomialCoeffL1_ksSpectatorCoefficientPolynomial
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (γ : Fin 3 →₀ ℕ) :
    polynomialCoeffL1 (ksSpectatorCoefficientPolynomial P γ) ≤ polynomialCoeffL1 P := by
  classical
  let f : (Fin 4 →₀ ℕ) → (Fin 4 ⊕ Fin 3 →₀ ℕ) := fun α => Finsupp.sumElim α γ
  have hf : Function.Injective f := by
    intro α β h
    ext i
    exact congrArg (fun d : Fin 4 ⊕ Fin 3 →₀ ℕ => d (Sum.inl i)) h
  have hs : (ksSpectatorCoefficientPolynomial P γ).support.image f ⊆ P.support := by
    intro d hd
    obtain ⟨α,hα,rfl⟩ := Finset.mem_image.mp hd
    apply mem_support_iff.mpr
    have hne := mem_support_iff.mp hα
    simpa only [ksSpectatorCoefficientPolynomial_coeff] using hne
  rw [polynomialCoeffL1_eq_sum,polynomialCoeffL1_eq_sum]
  calc
    _ = ∑ d ∈ (ksSpectatorCoefficientPolynomial P γ).support.image f, ‖P.coeff d‖ := by
      rw [Finset.sum_image (fun α _ β _ h => hf h)]
      exact Finset.sum_congr rfl (fun α _ => by rw [ksSpectatorCoefficientPolynomial_coeff])
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hs (fun _ _ _ => norm_nonneg _)

theorem ksSpectatorCoefficientPolynomial_coefficient_bound
    (P : MvPolynomial (Fin 4 ⊕ Fin 3) ℂ) (γ : Fin 3 →₀ ℕ) (α : Fin 4 →₀ ℕ) :
    ‖(ksSpectatorCoefficientPolynomial P γ).coeff α‖ ≤ polynomialCoeffL1 P := by
  rw [ksSpectatorCoefficientPolynomial_coeff]
  exact polynomialCoeffL1_coefficient_bound P (Finsupp.sumElim α γ)

end TheoremT.Continuum
