import CompactGrushinRadialComponentBounds_v1
import GrushinFactorialGraphCoefficient_v1
import GrushinFactorialLowDegreeCases_v1
import SmoothFactorialJet_v1

/-! A common explicit graph coefficient for all genuine coordinate
components of order at most two.  The support slab half-width R is kept
separate from any Euclidean radius used to bound extra monomial weights.
This coefficient is a safe formal variant, not an optimized paper constant.
The zero and first-Y integral bounds remain explicit in this helper; the
final compact graph theorem supplies them from the proved slab estimates. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem compact_smooth_factorial_radial_integral_bound
    {c : ℝ} (hc : 0 < c) {G : Space (Fin 3) → ℂ}
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G)
    {R : ℝ} (hR : 0 < R)
    (hinput : (∫ p, ‖G p‖^2 ∂(volume : Measure (Space (Fin 3)))) ≤
      (4*R^2)^2*(∫ p, ‖euclideanGrushin c G p‖^2))
    (hY : (∑ i : Fin 4, ∫ p, ‖partialYDirectional G (oscillatorBasis i) p‖^2) ≤
      (4*R^2)*(∫ p, ‖euclideanGrushin c G p‖^2))
    (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (horder : (∑ i, α i)+(∑ j, β j) ≤ 2) :
    (∫ p, ‖(‖p.1‖^(factorialOuterRadialOrder α β) : ℝ) • smoothFactorialJet G α β p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤
      (factorialGraphCoefficient R c)^2*(∫ p, ‖euclideanGrushin c G p‖^2
      ∂(volume : Measure (Space (Fin 3)))) := by
  have hcomp := compact_grushin_radial_component_bounds hc.le hG hcG
  simp only [← Measure.volume_eq_prod] at hcomp
  let C := factorialGraphCoefficient R c
  let E := ∫ p, ‖euclideanGrushin c G p‖^2 ∂(volume : Measure (Space (Fin 3)))
  have hE : 0 ≤ E := integral_nonneg (fun _ => sq_nonneg _)
  obtain ⟨hC0,hCY,hC2,hcC2⟩ := factorialGraphCoefficient_bounds hR hc
  change 4*R^2 ≤ C at hC0
  change 2*R ≤ C at hCY
  change 2 ≤ C at hC2
  change 2 ≤ c*C at hcC2
  have hC0sq := pow_le_pow_left₀ (by positivity : 0 ≤ 4*R^2) hC0 2
  have hCYsq := pow_le_pow_left₀ (by positivity : 0 ≤ 2*R) hCY 2
  have hC2sq : 4 ≤ C^2 := by nlinarith
  have hcC2sq : 4 ≤ c^2*C^2 := by nlinarith [sq_nonneg (c*C-2)]
  have hcCprod : 4 ≤ c*C^2 := by nlinarith [mul_le_mul hcC2 hC2 (by norm_num : (0:ℝ) ≤ 2) (by linarith : 0 ≤ c*C)]
  have hs0 : (∫ p, ‖G p‖^2 ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    hinput.trans (mul_le_mul_of_nonneg_right hC0sq hE)
  have hsY (i : Fin 4) : (∫ p, ‖partialYDirectional G (oscillatorBasis i) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E := by
    have ht := Finset.single_le_sum (s := Finset.univ)
      (f := fun i : Fin 4 => ∫ p, ‖partialYDirectional G (oscillatorBasis i) p‖^2
        ∂(volume : Measure (Space (Fin 3))))
      (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) (Finset.mem_univ i)
    exact (ht.trans hY).trans (mul_le_mul_of_nonneg_right (by nlinarith : 4*R^2 ≤ C^2) hE)
  have hsT (j : Fin 3) : (∫ p, ‖partialTDirectional G (oscillatorBasis j) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    positive_weighted_square_bound (b := 1) (by positivity : 0 < 16*c) hE (by nlinarith) (by simpa only [one_mul,E] using hcomp.1 j)
  have hsYY (i j : Fin 4) : (∫ p, ‖partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    (hcomp.2.1 i j).trans (mul_le_mul_of_nonneg_right (by linarith : (3/2:ℝ) ≤ C^2) hE)
  have hsYT (i : Fin 4) (j : Fin 3) : (∫ p, ‖(‖p.1‖:ℝ) •
      partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    positive_weighted_square_bound (b := 3/2) (by positivity : 0 < 2*c) hE (by nlinarith) (hcomp.2.2.1 i j)
  have hsTT (i j : Fin 3) : (∫ p, ‖(‖p.1‖^2:ℝ) •
      partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂(volume : Measure (Space (Fin 3)))) ≤ C^2*E :=
    positive_weighted_square_bound (b := 3/2) (by positivity : 0 < c^2) hE (by nlinarith) (hcomp.2.2.2 i j)
  rcases factorial_outer_derivative_six_cases α β horder with
    ⟨rfl,rfl⟩ | ⟨i,rfl,rfl⟩ | ⟨j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩ | ⟨i,j,rfl,rfl⟩
  · simpa [factorialOuterRadialOrder,smoothFactorialJet_zero] using hs0
  · simpa [factorialOuterRadialOrder,smoothFactorialJet_single_y hG] using hsY i
  · simpa [factorialOuterRadialOrder,smoothFactorialJet_single_t hG] using hsT j
  · simpa [factorialOuterRadialOrder,Finset.sum_add_distrib,smoothFactorialJet_double_y hG] using hsYY i j
  · simpa [factorialOuterRadialOrder,smoothFactorialJet_mixed hG] using hsYT i j
  · simpa [factorialOuterRadialOrder,Finset.sum_add_distrib,smoothFactorialJet_double_t hG] using hsTT i j

end TheoremT.Continuum.WeakGrushin
