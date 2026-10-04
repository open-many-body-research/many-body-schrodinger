import ManyBody.S8.Internal.RealRationalAmbientProfile
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Analysis.Calculus.ContDiff.Bounds
/-! Genuine selected-distance reflection and rational polynomial averaging.

The actual linear reflection preserves the literal coordinate max norm.
Analytic power-series composition transports every actual ordered derivative;
its operator norm contracts derivative differences. Averaging a literal finite
rational polynomial with this reflection gives literal rational coefficients,
exact evenness, and the SAME uniform real C0/C1/C2 error on every centered
reflection-invariant box. No output parity or derivative identity is assumed. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped Topology BigOperators ContDiff
namespace ManyBody.S8

def realDistanceReflectCLM (j : Fin 3) : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ) :=
  ContinuousLinearMap.pi fun k =>
    if k=j then -(ContinuousLinearMap.proj k) else ContinuousLinearMap.proj k

@[simp] theorem realDistanceReflectCLM_apply (j : Fin 3) (p : Fin 3 → ℝ) (k : Fin 3) :
    realDistanceReflectCLM j p k=if k=j then -p k else p k := by
  simp [realDistanceReflectCLM]
  split_ifs <;> rfl

theorem realDistanceReflectCLM_norm (j : Fin 3) (p : Fin 3 → ℝ) :
    ‖realDistanceReflectCLM j p‖=‖p‖ := by
  have hk (k : Fin 3) : ‖realDistanceReflectCLM j p k‖=‖p k‖ := by
    simp only [realDistanceReflectCLM_apply]
    split_ifs <;> simp
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun k =>
      (hk k).le.trans (norm_le_pi_norm p k)
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun k =>
      (hk k).symm.le.trans (norm_le_pi_norm (realDistanceReflectCLM j p) k)

theorem realDistanceReflectCLM_involutive (j : Fin 3) (p : Fin 3 → ℝ) :
    realDistanceReflectCLM j (realDistanceReflectCLM j p)=p := by
  ext k
  simp only [realDistanceReflectCLM_apply]
  split_ifs <;> simp

theorem realDistanceReflectCLM_center {j : Fin 3} {a : Fin 3 → ℝ} (ha : a j=0) :
    realDistanceReflectCLM j a=a := by
  ext k
  simp only [realDistanceReflectCLM_apply]
  split_ifs with h
  · subst k; simp [ha]
  · rfl

theorem realDistanceReflectCLM_box {j : Fin 3} {a p : Fin 3 → ℝ} {b : ℝ}
    (ha : a j=0) (hp : ‖p-a‖≤b) : ‖realDistanceReflectCLM j p-a‖≤b := by
  rw [←realDistanceReflectCLM_center ha,←map_sub,realDistanceReflectCLM_norm]
  exact hp

theorem real_iteratedFDeriv_linear_restriction
    {f : (Fin 3 → ℝ) → ℝ} (L : (Fin 3 → ℝ) →L[ℝ] (Fin 3 → ℝ))
    {p : Fin 3 → ℝ} (hf : AnalyticAt ℝ f (L p))
    (n : ℕ) (v : Fin n → (Fin 3 → ℝ)) :
    iteratedFDeriv ℝ n (f ∘ L) p v=iteratedFDeriv ℝ n f (L p) (fun k => L (v k)) := by
  obtain ⟨P,⟨R,hP⟩⟩ := hf
  have hc := hP.compContinuousLinearMap (u:=L)
  rw [hc.iteratedFDeriv_eq_sum_of_completeSpace v,
    hP.iteratedFDeriv_eq_sum_of_completeSpace (fun k => L (v k))]
  apply Finset.sum_congr rfl
  intro σ hσ
  rfl

theorem real_reflected_derivative_difference_le
    {f g : (Fin 3 → ℝ) → ℝ} {p : Fin 3 → ℝ} (j : Fin 3)
    (hf : AnalyticAt ℝ f (realDistanceReflectCLM j p))
    (hg : AnalyticAt ℝ g (realDistanceReflectCLM j p)) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (f ∘ realDistanceReflectCLM j) p-
      iteratedFDeriv ℝ n (g ∘ realDistanceReflectCLM j) p‖≤
      ‖iteratedFDeriv ℝ n f (realDistanceReflectCLM j p)-
        iteratedFDeriv ℝ n g (realDistanceReflectCLM j p)‖ := by
  apply (iteratedFDeriv ℝ n (f ∘ realDistanceReflectCLM j) p-
    iteratedFDeriv ℝ n (g ∘ realDistanceReflectCLM j) p).opNorm_le_bound (norm_nonneg _)
  intro v
  rw [sub_apply,real_iteratedFDeriv_linear_restriction _ hf,
    real_iteratedFDeriv_linear_restriction _ hg]
  simpa only [sub_apply,realDistanceReflectCLM_norm] using
    (iteratedFDeriv ℝ n f (realDistanceReflectCLM j p)-
      iteratedFDeriv ℝ n g (realDistanceReflectCLM j p)).le_opNorm
        (fun k => realDistanceReflectCLM j (v k))

theorem realDistanceMonomial_reflect (j : Fin 3) (α : DistanceMultiIndex) (p : Fin 3 → ℝ) :
    realDistanceMonomial α (realDistanceReflectCLM j p)=
      (-1:ℝ)^(α j)*realDistanceMonomial α p := by
  fin_cases j <;>
    simp [realDistanceMonomial,Fin.prod_univ_three,realDistanceReflectCLM_apply,
       ] <;> rw [neg_pow] <;> ring

def reflectedRationalDistanceCoefficients (j : Fin 3) (r : DistanceMultiIndex → ℚ)
    (α : DistanceMultiIndex) : ℚ := (r α+(-1:ℚ)^(α j)*r α)/2

theorem reflected_rational_distance_polynomial_average (j : Fin 3)
    (s : Finset DistanceMultiIndex) (r : DistanceMultiIndex → ℚ) (p : Fin 3 → ℝ) :
    realDistancePolynomial s (fun α => (reflectedRationalDistanceCoefficients j r α:ℝ)) p=
      (1/2:ℝ)*(realDistancePolynomial s (fun α => (r α:ℝ)) p+
        realDistancePolynomial s (fun α => (r α:ℝ)) (realDistanceReflectCLM j p)) := by
  unfold realDistancePolynomial
  simp_rw [realDistanceMonomial_reflect]
  rw [←Finset.sum_add_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  simp only [reflectedRationalDistanceCoefficients,Rat.cast_div,Rat.cast_add,
    Rat.cast_mul,Rat.cast_pow,Rat.cast_neg,Rat.cast_one,Rat.cast_ofNat,smul_eq_mul]
  ring

theorem reflected_rational_distance_polynomial_even (j : Fin 3)
    (s : Finset DistanceMultiIndex) (r : DistanceMultiIndex → ℚ) (p : Fin 3 → ℝ) :
    realDistancePolynomial s (fun α => (reflectedRationalDistanceCoefficients j r α:ℝ))
        (realDistanceReflectCLM j p)=
      realDistancePolynomial s (fun α => (reflectedRationalDistanceCoefficients j r α:ℝ)) p := by
  rw [reflected_rational_distance_polynomial_average,
    reflected_rational_distance_polynomial_average,realDistanceReflectCLM_involutive]
  ring

#print axioms real_reflected_derivative_difference_le
#print axioms reflected_rational_distance_polynomial_average
#print axioms reflected_rational_distance_polynomial_even

theorem realDistancePolynomial_analytic (s : Finset DistanceMultiIndex)
    (c : DistanceMultiIndex → ℝ) (p : Fin 3 → ℝ) :
    AnalyticAt ℝ (realDistancePolynomial s c) p := by
  unfold realDistancePolynomial realDistanceMonomial
  exact Finset.analyticAt_fun_sum s fun α _ =>
    (Finset.analyticAt_fun_prod Finset.univ fun j _ =>
      ((ContinuousLinearMap.proj j : (Fin 3 → ℝ) →L[ℝ] ℝ).analyticAt p).pow (α j)).const_smul
        (c := c α)

theorem rational_even_distance_polynomial_uniform_C2
    {f : (Fin 3 → ℝ) → ℝ} (j : Fin 3) {a : Fin 3 → ℝ} {b η : ℝ}
    (ha : a j=0)
    (hf : ∀ p : Fin 3 → ℝ, ‖p-a‖≤b → AnalyticAt ℝ f p)
    (heven : ∀ p : Fin 3 → ℝ, f (realDistanceReflectCLM j p)=f p)
    (s : Finset DistanceMultiIndex) (r : DistanceMultiIndex → ℚ)
    (happrox : ∀ p : Fin 3 → ℝ, ‖p-a‖≤b → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ (k:ℕ) f p-
        iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s (fun α => (r α:ℝ))) p‖<η) :
    (∀ p : Fin 3 → ℝ,
      realDistancePolynomial s (fun α => (reflectedRationalDistanceCoefficients j r α:ℝ))
          (realDistanceReflectCLM j p)=
        realDistancePolynomial s (fun α => (reflectedRationalDistanceCoefficients j r α:ℝ)) p) ∧
    (∀ p : Fin 3 → ℝ, ‖p-a‖≤b → ∀ k : Fin 3,
      ‖iteratedFDeriv ℝ (k:ℕ) f p-
        iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s
          (fun α => (reflectedRationalDistanceCoefficients j r α:ℝ))) p‖<η) := by
  refine ⟨reflected_rational_distance_polynomial_even j s r,?_⟩
  intro p hp k
  let P := realDistancePolynomial s (fun α => (r α:ℝ))
  have hP : ContDiff ℝ (k:ℕ) P := (realDistancePolynomial_contDiff s _).of_le (by simp)
  have hPr : ContDiff ℝ (k:ℕ) (P ∘ realDistanceReflectCLM j) := hP.comp_continuousLinearMap
  have hEq : realDistancePolynomial s
      (fun α => (reflectedRationalDistanceCoefficients j r α:ℝ))=
      (1/2:ℝ) • (P+P ∘ realDistanceReflectCLM j) := by
    funext q
    exact reflected_rational_distance_polynomial_average j s r q
  have hsum : ContDiffAt ℝ (k:ℕ) (P+P ∘ realDistanceReflectCLM j) p :=
    (hP.add hPr).contDiffAt
  have hscalar := iteratedFDeriv_const_smul_apply
    (f := P+P ∘ realDistanceReflectCLM j) (a := (1/2:ℝ)) hsum
  have hadd := iteratedFDeriv_add_apply (x:=p) (f := P) (g := P ∘ realDistanceReflectCLM j)
    hP.contDiffAt hPr.contDiffAt
  rw [hEq,hscalar,hadd]
  have hfp : f ∘ realDistanceReflectCLM j=f := funext heven
  have hpr : ‖iteratedFDeriv ℝ (k:ℕ) f p-
      iteratedFDeriv ℝ (k:ℕ) (P ∘ realDistanceReflectCLM j) p‖<η := by
    calc _=‖iteratedFDeriv ℝ (k:ℕ) (f ∘ realDistanceReflectCLM j) p-
        iteratedFDeriv ℝ (k:ℕ) (P ∘ realDistanceReflectCLM j) p‖ := by rw [hfp]
         _≤‖iteratedFDeriv ℝ (k:ℕ) f (realDistanceReflectCLM j p)-
          iteratedFDeriv ℝ (k:ℕ) P (realDistanceReflectCLM j p)‖ :=
          real_reflected_derivative_difference_le j (hf _ (realDistanceReflectCLM_box ha hp))
            (realDistancePolynomial_analytic s _ _) _
         _<η := happrox _ (realDistanceReflectCLM_box ha hp) k
  have hh : iteratedFDeriv ℝ (k:ℕ) f p-
      (1/2:ℝ) • (iteratedFDeriv ℝ (k:ℕ) P p+
        iteratedFDeriv ℝ (k:ℕ) (P ∘ realDistanceReflectCLM j) p)=
      (1/2:ℝ) • ((iteratedFDeriv ℝ (k:ℕ) f p-iteratedFDeriv ℝ (k:ℕ) P p)+
        (iteratedFDeriv ℝ (k:ℕ) f p-
          iteratedFDeriv ℝ (k:ℕ) (P ∘ realDistanceReflectCLM j) p)) := by module
  rw [hh,norm_smul]
  have hb := norm_add_le (iteratedFDeriv ℝ (k:ℕ) f p-iteratedFDeriv ℝ (k:ℕ) P p)
    (iteratedFDeriv ℝ (k:ℕ) f p-iteratedFDeriv ℝ (k:ℕ) (P ∘ realDistanceReflectCLM j) p)
  have hpa := happrox p hp k
  norm_num
  linarith

#print axioms rational_even_distance_polynomial_uniform_C2
end ManyBody.S8
