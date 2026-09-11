import RegularizedCoulombCusp_v1
import RegularizedLinearRadiusError_v1
import StrictPairIncidence_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem finite_linear_radius_regularization_error {N : ℕ} {ι : Type*} [Fintype ι]
    (A : ι → Configuration N →L[ℝ] Position) {δ : ℝ} (hδ : 0 < δ) (x : Configuration N) :
    |(∑ i, regularizedLinearRadius (A i) δ x)-(∑ i, ‖A i x‖)| ≤
      (Fintype.card ι:ℝ)*Real.sqrt δ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i, |regularizedLinearRadius (A i) δ x-‖A i x‖| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, Real.sqrt δ := Finset.sum_le_sum (fun i _ => regularizedLinearRadius_sub_norm_bound (A i) hδ x)
    _ = _ := by simp

def cuspRegularizationCoefficient (N : ℕ) (Z : ℝ) : ℝ := |Z| * N+(N.choose 2:ℝ)/2

theorem cuspRegularizationCoefficient_nonneg (N : ℕ) (Z : ℝ) :
    0 ≤ cuspRegularizationCoefficient N Z := by unfold cuspRegularizationCoefficient; positivity

theorem coulombCusp_regularization_error (N : ℕ) (Z : ℝ) {δ : ℝ} (hδ : 0 < δ)
    (x : Configuration N) :
    |regularizedCoulombCusp N Z δ x-coulombCusp N Z x| ≤
      cuspRegularizationCoefficient N Z*Real.sqrt δ := by
  have hn : |(∑ i : Fin N, regularizedLinearRadius (electronPositionCLM i) δ x)-
      (∑ i : Fin N, ‖position x i‖)| ≤ (N:ℝ)*Real.sqrt δ := by
    simpa only [electronPositionCLM_apply,Fintype.card_fin] using
      finite_linear_radius_regularization_error (fun i : Fin N => electronPositionCLM i) hδ x
  have hp : |(∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      regularizedLinearRadius (pairDifferenceCLM i j) δ x)-
      (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        ‖position x i-position x j‖)| ≤ (N.choose 2:ℝ)*Real.sqrt δ := by
    rw [← strictElectronPair_sum_real (fun i j => regularizedLinearRadius (pairDifferenceCLM i j) δ x),
      ← strictElectronPair_sum_real (fun i j => ‖position x i-position x j‖)]
    simpa only [pairDifferenceCLM_apply,strictElectronPair_card] using
      finite_linear_radius_regularization_error
        (fun q : StrictElectronPair N => pairDifferenceCLM q.val.1 q.val.2) hδ x
  have he : regularizedCoulombCusp N Z δ x-coulombCusp N Z x =
      -Z*((∑ i : Fin N, regularizedLinearRadius (electronPositionCLM i) δ x)-
        (∑ i : Fin N, ‖position x i‖))+
      (1/2:ℝ)*((∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        regularizedLinearRadius (pairDifferenceCLM i j) δ x)-
        (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
          ‖position x i-position x j‖)) := by
    unfold regularizedCoulombCusp coulombCusp
    ring
  rw [he]
  have ha := abs_add_le
    (-Z*((∑ i : Fin N, regularizedLinearRadius (electronPositionCLM i) δ x)-
      (∑ i : Fin N, ‖position x i‖)))
    ((1/2:ℝ)*((∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
      regularizedLinearRadius (pairDifferenceCLM i j) δ x)-
      (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i<j),
        ‖position x i-position x j‖)))
  simp only [abs_mul,abs_neg,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/2)] at ha
  have hb := add_le_add (mul_le_mul_of_nonneg_left hn (abs_nonneg Z))
    (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ) ≤ 1/2))
  exact (ha.trans hb).trans_eq (by unfold cuspRegularizationCoefficient; ring)

#print axioms coulombCusp_regularization_error
end TheoremT.Continuum
