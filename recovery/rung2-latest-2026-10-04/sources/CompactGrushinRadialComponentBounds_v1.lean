import GrushinWeightedTHessianIdentity_v1
import CompactGrushinTangentialBound_v1
import ActualL2IntegralCauchy_v1

/-! Individual actual coordinate derivatives controlled by the compact
Grushin graph.  The mixed term has exactly one radial weight; the TT term
has exactly two.  No unweighted TT estimate is asserted at y=0. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem finite_double_term_le_sum {ι ν : Type*} [Fintype ι] [Fintype ν]
    (f : ι → ν → ℝ) (hf : ∀ i j, 0 ≤ f i j) (i : ι) (j : ν) :
    f i j ≤ ∑ a, ∑ b, f a b := by
  classical
  exact (Finset.single_le_sum (fun b _ => hf i b) (Finset.mem_univ j)).trans
    (Finset.single_le_sum (fun a _ => Finset.sum_nonneg (fun b _ => hf a b)) (Finset.mem_univ i))

theorem compact_grushin_radial_component_bounds {c : ℝ} (hc : 0 ≤ c)
    {G : EuclideanSpace ℝ (Fin 4) × EuclideanSpace ℝ κ → ℂ}
    (hG : ContDiff ℝ ∞ G) (hcG : HasCompactSupport G) :
    (∀ j : κ, 16*c*(∫ p, ‖partialTDirectional G (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      ∫ p, ‖euclideanGrushin c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ∧
    (∀ i j : Fin 4, (∫ p, ‖partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      (3/2 : ℝ)*(∫ p, ‖euclideanGrushin c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))) ∧
    (∀ (i : Fin 4) (j : κ), 2*c*(∫ p,
      ‖(‖p.1‖ : ℝ) • partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      (3/2 : ℝ)*(∫ p, ‖euclideanGrushin c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))) ∧
    (∀ i j : κ, c^2*(∫ p,
      ‖(‖p.1‖^2 : ℝ) • partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) ≤
      (3/2 : ℝ)*(∫ p, ‖euclideanGrushin c G p‖^2 ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))) := by
  have hfull := compact_grushin_full_weighted_hessian_bound hc hG hcG
  have hY0 : 0 ≤ ∑ i : Fin 4, ∑ j : Fin 4, ∫ p,
      ‖partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
  have hT0 : 0 ≤ ∑ i : κ, ∑ j : κ, ∫ p,
      ‖(c*‖p.1‖^2) • partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume) :=
    Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)))
  have hM0 : 0 ≤ 2*c*(∑ i : Fin 4, ∑ j : κ, ∫ p, ‖p.1‖^2*
      ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
      ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg (fun _ _ => Finset.sum_nonneg (fun _ _ =>
      integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))))
  refine ⟨?_,?_,?_,?_⟩
  · intro j
    have hs := Finset.single_le_sum (s := Finset.univ)
      (f := fun j : κ => ∫ p, ‖partialTDirectional G (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))
      (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) (Finset.mem_univ j)
    exact (mul_le_mul_of_nonneg_left hs (by positivity)).trans (compact_grushin_tangential_bound hc hG hcG)
  · intro i j
    have hs := finite_double_term_le_sum
      (fun i j : Fin 4 => ∫ p, ‖partialYDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))
      (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) i j
    linarith
  · intro i j
    have hs := finite_double_term_le_sum
      (fun (i : Fin 4) (j : κ) => ∫ p, ‖p.1‖^2*
        ‖partialTDirectional (partialYDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))
      (fun _ _ => integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))) i j
    have hs' := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2*c)
    simp only [norm_smul,Real.norm_eq_abs,abs_norm,mul_pow]
    linarith
  · intro i j
    have hs := finite_double_term_le_sum
      (fun i j : κ => ∫ p, ‖(c*‖p.1‖^2) •
        partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume))
      (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) i j
    have he : (∫ p, ‖(c*‖p.1‖^2) • partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) =
        c^2*(∫ p, ‖(‖p.1‖^2 : ℝ) • partialTDirectional (partialTDirectional G (oscillatorBasis i)) (oscillatorBasis j) p‖^2
        ∂((volume : Measure (EuclideanSpace ℝ (Fin 4))).prod volume)) := by
      simp only [mul_smul,norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,mul_assoc]
      rw [integral_const_mul]
    rw [he] at hs
    linarith

end TheoremT.Continuum
