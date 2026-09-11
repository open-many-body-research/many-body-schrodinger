import CompactWeightedDirectionalGreen_v1
import EuclideanOscillatorOperator_v1

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff RealInnerProductSpace
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def oscillatorLaplacian (u : EuclideanSpace ℝ ι → ℂ) (x : EuclideanSpace ℝ ι) : ℂ :=
  ∑ k : ι, oscillatorPartial (oscillatorPartial u k) k x

theorem euclidean_oscillator_cross_pointwise (u : EuclideanSpace ℝ ι → ℂ)
    (x : EuclideanSpace ℝ ι) :
    inner ℝ (-(oscillatorLaplacian u x)) (‖x‖^2 • u x) =
      ∑ k : ι, ∑ j : ι, inner ℝ (-(oscillatorPartial (oscillatorPartial u k) k x)) ((x j)^2 • u x) := by
  simp only [oscillatorLaplacian,inner_neg_left,real_inner_smul_right,sum_inner]
  rw [EuclideanSpace.real_norm_sq_eq]
  simp only [Finset.mul_sum,← Finset.sum_mul,Finset.sum_neg_distrib]

theorem euclidean_oscillator_weight_pointwise (u : EuclideanSpace ℝ ι → ℂ)
    (x : EuclideanSpace ℝ ι) :
    (∑ k : ι, ∑ j : ι, (x j)^2*‖oscillatorPartial u k x‖^2) =
      ‖x‖^2*(∑ k : ι, ‖oscillatorPartial u k x‖^2) := by
  simp only [← Finset.sum_mul]
  rw [← EuclideanSpace.real_norm_sq_eq,Finset.mul_sum]

theorem compact_euclidean_oscillator_cross {u : EuclideanSpace ℝ ι → ℂ}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) :
    (∫ x, inner ℝ (-(oscillatorLaplacian u x)) (‖x‖^2 • u x)) =
      (∫ x, ‖x‖^2*(∑ k : ι, ‖oscillatorPartial u k x‖^2))-
        (Fintype.card ι : ℝ)*(∫ x, ‖u x‖^2) := by
  let C : ι → ι → EuclideanSpace ℝ ι → ℝ := fun k j x =>
    inner ℝ (-(oscillatorPartial (oscillatorPartial u k) k x)) ((x j)^2 • u x)
  let W : ι → ι → EuclideanSpace ℝ ι → ℝ := fun k j x => (x j)^2*‖oscillatorPartial u k x‖^2
  have hC (k j : ι) : Integrable (C k j) volume := by
    have hL : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => x j) := (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
    have hP : ContDiff ℝ ∞ (fun x : EuclideanSpace ℝ ι => (x j)^2) := hL.pow 2
    exact compact_real_inner_integrable_general
      (oscillatorPartial_contDiff (oscillatorPartial_contDiff hu k) k).continuous.neg
      (hP.smul hu).continuous (oscillatorPartial_compact (oscillatorPartial_compact hc k) k).neg
  have hW (k j : ι) : Integrable (W k j) volume := by
    have hP : Continuous (fun x : EuclideanSpace ℝ ι => (x j)^2) := (EuclideanSpace.proj j).continuous.pow 2
    apply (hP.mul ((oscillatorPartial_contDiff hu k).continuous.norm.pow 2)).integrable_of_hasCompactSupport
    apply (oscillatorPartial_compact hc k).mono
    intro x hx
    change oscillatorPartial u k x ≠ 0
    intro hz
    exact hx (by simp [W,hz])
  have he (k j : ι) : (∫ x,C k j x) = (∫ x,W k j x)-
      ((oscillatorBasis k) j)^2*(∫ x,‖u x‖^2) :=
    compact_weighted_directional_green (EuclideanSpace.proj j) (oscillatorBasis k) hu hc
  simp_rw [euclidean_oscillator_cross_pointwise]
  change (∫ x,∑ k : ι,∑ j : ι,C k j x) = _
  rw [integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ => hC k j))]
  simp_rw [integral_finsetSum _ (fun j _ => hC _ j),he,Finset.sum_sub_distrib]
  have hdiag (k : ι) : (∑ j : ι,((oscillatorBasis k) j)^2*(∫ x,‖u x‖^2)) = (∫ x,‖u x‖^2) := by
    simp [oscillatorBasis]
  simp_rw [hdiag]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  congr 1
  have hWi (k : ι) : (∑ j : ι, ∫ x,W k j x) = (∫ x,∑ j : ι,W k j x) :=
    (integral_finsetSum _ (fun j _ => hW k j)).symm
  simp_rw [hWi]
  rw [← integral_finsetSum _ (fun k _ => integrable_finsetSum _ (fun j _ => hW k j))]
  apply integral_congr_ae
  filter_upwards [] with x
  exact euclidean_oscillator_weight_pointwise u x

#print axioms compact_euclidean_oscillator_cross
end TheoremT.Continuum
