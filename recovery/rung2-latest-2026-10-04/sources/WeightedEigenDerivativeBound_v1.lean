import ScalarFormKineticBound_v1
import WeightedMultiplierBound_v1

/-! A bounded smooth weight controls weighted actual eigenfunction derivatives.
No derivative decay is assumed. The estimate follows from the physical weak
form identity, Hardy's form bound and the actual weak product rule. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem scalar_eigen_weighted_derivative_bound {N : ℕ} {Z E : ℝ} {f : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    (d : Coordinate N → SpatialL2 N) (hd : ∀ k, WeakPartial f (d k) k)
    (χ : Configuration N → ℝ) (hχ : ContDiff ℝ ∞ χ) (hm : MemLp χ ⊤ volume)
    (hdm : ∀ k : Coordinate N,
      MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume)
    (k : Coordinate N) :
    ‖boundedRealMul χ hm (d k)‖^2 ≤
      8*(|E|+(2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ)))^2) * ‖boundedRealMul χ hm f‖^2 +
      6 * (∑ l : Coordinate N,
        ‖boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector l)) (hdm l) f‖^2) := by
  let M := boundedRealMul χ hm
  let B : Coordinate N → SpatialL2 N := fun l =>
    boundedRealMul (fun x => fderiv ℝ χ x (coordinateVector l)) (hdm l) f
  let D : Coordinate N → SpatialL2 N := fun l => M (d l) + B l
  have hD (l : Coordinate N) : WeakPartial (M f) (D l) l :=
    weakPartial_boundedRealMul (hd l) χ hχ hm (hdm l)
  have hkin := scalar_form_kinetic_bound D hD
    (scalar_eigen_weighted_form_value hg χ hχ hm hdm)
  have hkD := Finset.single_le_sum (fun l _ => sq_nonneg ‖D l‖) (Finset.mem_univ k)
  have hkB := Finset.single_le_sum (fun l _ => sq_nonneg ‖B l‖) (Finset.mem_univ k)
  have he : M (d k) = D k - B k := by dsimp [D]; abel
  have hn : ‖M (d k)‖ ≤ ‖D k‖+‖B k‖ := he ▸ norm_sub_le _ _
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  have hE := mul_le_mul_of_nonneg_right (le_abs_self E) (sq_nonneg ‖M f‖)
  change ‖M (d k)‖^2 ≤
    8*(|E|+(2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ)))^2)*‖M f‖^2+6*(∑ l, ‖B l‖^2)
  change (∑ l, ‖D l‖^2) ≤ 4*(E*‖M f‖^2+(1/2 : ℝ)*(∑ l, ‖B l‖^2)+
    (2*(|Z| *(N : ℝ)+(N.choose 2 : ℝ)))^2*‖M f‖^2) at hkin
  nlinarith [sq_nonneg (‖D k‖-‖B k‖)]

#print axioms scalar_eigen_weighted_derivative_bound
end TheoremT.Continuum
