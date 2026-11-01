import CompactSlabPoincare_v1
import NonnegativeEnergySlabBound_v1
import CompactGrushinEnergyCauchy_v1

/-! Actual compact Grushin graph control of the input and first spatial
derivatives on a support slab. The support inequality and energy identity
are proved dependencies; no norm or coercivity bound is an input. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem compact_grushin_slab_graph_bounds {c : ℝ} (hc0 : 0 ≤ c)
    (i : ι) {G : EuclideanSpace ℝ ι × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hc : HasCompactSupport G)
    {R : ℝ} (hR : 0 < R) (hs : ∀ p, G p ≠ 0 → |p.1 i| ≤ R) :
    (∫ p, ‖G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) ≤
      (4*R^2)^2 * (∫ p, ‖euclideanGrushin c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) ∧
    grushinGradientEnergy c G ≤
      (4*R^2) * (∫ p, ‖euclideanGrushin c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) ∧
    (∑ j : ι, ∫ p, ‖partialYDirectional G (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) ≤
      (4*R^2) * (∫ p, ‖euclideanGrushin c G p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) := by
  have hY := grushin_y_gradient_le_energy hc0 G
  have hi : (∫ p, ‖partialYDirectional G (oscillatorBasis i) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume)) ≤
      grushinGradientEnergy c G := by
    apply le_trans _ hY
    exact Finset.single_le_sum
      (f := fun j : ι => ∫ p, ‖partialYDirectional G (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume))
      (fun j _ => integral_nonneg (fun p => sq_nonneg _)) (Finset.mem_univ i)
  have hsG := (compact_product_y_slab_poincare i hG hc hR hs).trans
    (mul_le_mul_of_nonneg_left hi (show 0 ≤ 4*R^2 from by positivity))
  obtain ⟨hinput,henergy⟩ := nonnegative_energy_slab_bounds
    (∫ p, ‖G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume))
    (grushinGradientEnergy c G)
    (∫ p, ‖euclideanGrushin c G p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ ι)).prod volume))
    (4*R^2) (grushin_gradient_energy_nonneg hc0 G)
    (integral_nonneg (fun p => sq_nonneg _)) (by positivity) hsG
    (compact_grushin_energy_square_le c hG hc)
  exact ⟨hinput,henergy,hY.trans henergy⟩

end TheoremT.Continuum
