import ManyBody.S8.Internal.RationalDistancePolynomial
import ManyBody.S8.Internal.ComplexTaylorTruncation
import ManyBody.S8.Internal.AmbientRealDerivativeTransport
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Analysis.Calculus.ContDiff.CPolynomial
/-! Genuine finite monomial representation of one real canonical Taylor polynomial.

Every multilinear diagonal expands over the actual real coordinate basis.
The finite word expansion is represented by a literal multivariate polynomial,
including the actual center translations. Its finite support becomes a finite
dictionary in the unshifted distance variables. Rational density therefore
approximates this ONE actual finite Taylor polynomial in real value and in
first/second operator norms, uniformly on a fixed bounded coordinate box. -/
set_option autoImplicit false
noncomputable section
open Set Metric
open scoped BigOperators ContDiff
namespace ManyBody.S8

theorem real_multilinear_coordinate_expansion {n : ℕ}
    (D : ContinuousMultilinearMap ℝ (fun _ : Fin n => Fin 3 → ℝ) ℝ)
    (p : Fin 3 → ℝ) :
    D (fun _ => p)=∑ w : Fin n → Fin 3,
      (∏ k, p (w k))*D (fun k => Pi.single (w k) 1) := by
  classical
  have hp : p=∑ j : Fin 3, p j • (Pi.single j 1 : Fin 3 → ℝ) := by
    ext j
    simp [Pi.single_apply]
  conv_lhs => rw [hp]
  change D.toMultilinearMap (fun _ : Fin n => ∑ j : Fin 3, p j • (Pi.single j 1 : Fin 3 → ℝ))= _
  rw [D.toMultilinearMap.map_sum]
  apply Finset.sum_congr rfl
  intro w hw
  exact D.map_smul_univ (fun k => p (w k)) (fun k => Pi.single (w k) 1)

def realTaylorCoefficient (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ)
    (n : ℕ) (h : Fin 3 → ℝ) : ℝ :=
  (n.factorial : ℝ)⁻¹ * iteratedFDeriv ℝ n f a (fun _ => h)

def realTaylorPolynomial (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ)
    (N : ℕ) (p : Fin 3 → ℝ) : ℝ :=
  ∑ n∈Finset.range N, realTaylorCoefficient f a n (p-a)

def realTaylorMvPolynomial (f : (Fin 3 → ℝ) → ℝ) (a : Fin 3 → ℝ)
    (N : ℕ) : MvPolynomial (Fin 3) ℝ :=
  ∑ n∈Finset.range N, ∑ w : Fin n → Fin 3,
    MvPolynomial.C ((n.factorial : ℝ)⁻¹ *
      iteratedFDeriv ℝ n f a (fun k => Pi.single (w k) 1)) *
      ∏ k, (MvPolynomial.X (w k)-MvPolynomial.C (a (w k)))

theorem realTaylorMvPolynomial_eval (f : (Fin 3 → ℝ) → ℝ)
    (a : Fin 3 → ℝ) (N : ℕ) (p : Fin 3 → ℝ) :
    MvPolynomial.eval p (realTaylorMvPolynomial f a N)=realTaylorPolynomial f a N p := by
  classical
  simp only [realTaylorMvPolynomial,map_sum,map_mul,map_prod,map_sub,
    MvPolynomial.eval_C,MvPolynomial.eval_X,realTaylorPolynomial,realTaylorCoefficient]
  apply Finset.sum_congr rfl
  intro n hn
  rw [real_multilinear_coordinate_expansion,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w hw
  simp only [Pi.sub_apply]
  ring

theorem mvPolynomial_finite_distance_dictionary (P : MvPolynomial (Fin 3) ℝ) :
    ∃ s : Finset DistanceMultiIndex, ∃ c : DistanceMultiIndex → ℝ,
      ∀ p, MvPolynomial.eval p P=realDistancePolynomial s c p := by
  classical
  let e : (Fin 3 →₀ ℕ) ≃ DistanceMultiIndex := Finsupp.equivFunOnFinite
  refine ⟨P.support.image e,fun α => P.coeff (e.symm α),?_⟩
  intro p
  rw [MvPolynomial.eval_eq']
  unfold realDistancePolynomial
  rw [Finset.sum_image (fun x _ y _ h => e.injective h)]
  apply Finset.sum_congr rfl
  intro d hd
  simp only [e.symm_apply_apply,smul_eq_mul,realDistanceMonomial]
  rfl

theorem realTaylorPolynomial_finite_distance_dictionary (f : (Fin 3 → ℝ) → ℝ)
    (a : Fin 3 → ℝ) (N : ℕ) :
    ∃ s : Finset DistanceMultiIndex, ∃ c : DistanceMultiIndex → ℝ,
      realTaylorPolynomial f a N=realDistancePolynomial s c := by
  obtain ⟨s,c,h⟩ := mvPolynomial_finite_distance_dictionary (realTaylorMvPolynomial f a N)
  exact ⟨s,c,funext fun p => (realTaylorMvPolynomial_eval f a N p).symm.trans (h p)⟩

theorem rational_realTaylorPolynomial_uniform_C2 (f : (Fin 3 → ℝ) → ℝ)
    (a : Fin 3 → ℝ) (N : ℕ) (b : ℝ) {ε : ℝ} (hε : 0<ε) :
    ∃ s : Finset DistanceMultiIndex, ∃ r : DistanceMultiIndex → ℚ,
      ∀ p : Fin 3 → ℝ, ‖p‖≤b → ∀ k : Fin 3,
        ‖iteratedFDeriv ℝ (k:ℕ) (realTaylorPolynomial f a N) p-
          iteratedFDeriv ℝ (k:ℕ) (realDistancePolynomial s (fun α => (r α:ℝ))) p‖<ε := by
  obtain ⟨s,c,h⟩ := realTaylorPolynomial_finite_distance_dictionary f a N
  obtain ⟨r,hr⟩ := rational_realDistancePolynomial_uniform_C2 s c b hε
  exact ⟨s,r,by rw [h]; exact hr⟩

#print axioms realTaylorPolynomial_finite_distance_dictionary
#print axioms rational_realTaylorPolynomial_uniform_C2
end ManyBody.S8
