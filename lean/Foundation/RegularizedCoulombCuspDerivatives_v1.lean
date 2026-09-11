import SmoothRealDerivativeSums_v1
import LinearRadiusWeakGradient_v1

noncomputable section
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem nuclear_regularized_sum_contDiff (N : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun x => ∑ i : Fin N, regularizedLinearRadius (electronPositionCLM i) δ x) :=
  ContDiff.sum (fun i _ => regularizedLinearRadius_contDiff _ hδ)

theorem pair_regularized_sum_contDiff {N : ℕ} (i : Fin N) {δ : ℝ} (hδ : 0 < δ) :
    ContDiff ℝ ∞ (fun x => ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      regularizedLinearRadius (pairDifferenceCLM i j) δ x) :=
  ContDiff.sum (fun j _ => regularizedLinearRadius_contDiff _ hδ)

theorem regularizedCoulombCusp_partial_sum (N : ℕ) (Z : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (x v : Configuration N) :
    fderiv ℝ (regularizedCoulombCusp N Z δ) x v =
      -Z*(∑ i : Fin N, fderiv ℝ (regularizedLinearRadius (electronPositionCLM i) δ) x v)+
      (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        fderiv ℝ (regularizedLinearRadius (pairDifferenceCLM i j) δ) x v) := by
  have hn := nuclear_regularized_sum_contDiff N hδ
  have hp : ContDiff ℝ ∞ (fun x => ∑ i : Fin N,
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        regularizedLinearRadius (pairDifferenceCLM i j) δ x) :=
    ContDiff.sum (fun i _ => pair_regularized_sum_contDiff i hδ)
  unfold regularizedCoulombCusp
  rw [real_fderiv_add_apply (contDiff_const.mul hn) (contDiff_const.mul hp),
    real_fderiv_const_mul_apply hn,real_fderiv_const_mul_apply hp,
    real_fderiv_finset_sum_apply _ (fun i _ => regularizedLinearRadius_contDiff (electronPositionCLM i) hδ),
    real_fderiv_finset_sum_apply _ (fun i _ => pair_regularized_sum_contDiff i hδ)]
  simp_rw [real_fderiv_finset_sum_apply _ (fun j _ => regularizedLinearRadius_contDiff (pairDifferenceCLM _ j) hδ)]

theorem regularizedCoulombCusp_mixed_sum (N : ℕ) (Z : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (x v w : Configuration N) :
    fderiv ℝ (fun y => fderiv ℝ (regularizedCoulombCusp N Z δ) y v) x w =
      -Z*(∑ i : Fin N, fderiv ℝ
        (fun y => fderiv ℝ (regularizedLinearRadius (electronPositionCLM i) δ) y v) x w)+
      (1/2:ℝ)*(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        fderiv ℝ (fun y => fderiv ℝ (regularizedLinearRadius (pairDifferenceCLM i j) δ) y v) x w) := by
  have hn := nuclear_regularized_sum_contDiff N hδ
  have hp : ContDiff ℝ ∞ (fun x => ∑ i : Fin N,
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        regularizedLinearRadius (pairDifferenceCLM i j) δ x) :=
    ContDiff.sum (fun i _ => pair_regularized_sum_contDiff i hδ)
  unfold regularizedCoulombCusp
  rw [real_mixed_add_apply (contDiff_const.mul hn) (contDiff_const.mul hp),
    real_mixed_const_mul_apply hn,real_mixed_const_mul_apply hp,
    real_mixed_finset_sum_apply _ (fun i _ => regularizedLinearRadius_contDiff (electronPositionCLM i) hδ),
    real_mixed_finset_sum_apply _ (fun i _ => pair_regularized_sum_contDiff i hδ)]
  simp_rw [real_mixed_finset_sum_apply _ (fun j _ => regularizedLinearRadius_contDiff (pairDifferenceCLM _ j) hδ)]

#print axioms regularizedCoulombCusp_partial_sum
#print axioms regularizedCoulombCusp_mixed_sum
end TheoremT.Continuum
