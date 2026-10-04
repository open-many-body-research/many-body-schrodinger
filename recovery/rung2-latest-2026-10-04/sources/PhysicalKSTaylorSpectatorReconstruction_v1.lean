import PhysicalKSTaylorSpectatorSeries_v1
import PhysicalKSComplexTaylorExtension_v1
import KSSpectatorHomogeneousReconstruction_v1
import SpectatorPolynomialSeriesReindex_v1

/-! The absolutely convergent extracted double series is the original joint
Taylor series. On the proved real ball it therefore has sum equal to the
actual physical KS base. Both reconstruction identities are conclusions. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators NNReal ENNReal
namespace TheoremT.Continuum
open MvPolynomial WeakGrushin

theorem physicalKSTaylorSpectatorFamily_grouped
    (f : Space (Fin 3) → ℂ) (x : Space (Fin 3)) (n : ℕ) :
    groupedHomogeneousSpectatorPolynomial (physicalKSTaylorSpectatorFamily f x) n =
      physicalKSTaylorPolynomial f x n := by
  have hfamily : physicalKSTaylorSpectatorFamily f x =
      (fun j γ => ksSpectatorCoefficientPolynomial
        (physicalKSTaylorPolynomial f x (j+∑ i : Fin 3, γ i))
        (Finsupp.equivFunOnFinite.symm γ)) := by
    funext j γ
    unfold physicalKSTaylorSpectatorFamily physicalKSTaylorSpectatorCoefficient
    have hdegree : (Finsupp.equivFunOnFinite.symm γ).degree = ∑ i : Fin 3, γ i := by
      simp [Finsupp.degree_eq_sum]
    rw [hdegree]
  rw [hfamily]
  exact ksSpectatorCoefficientPolynomial_grouped_reconstruct
    (physicalKSTaylorPolynomial f x) (physicalKSTaylorPolynomial_homogeneous f x) n

theorem physicalKSTaylorSpectatorFamily_hasSum_complex
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) {x : Space (Fin 3)}
    (hx : x ∈ rectangularOpenBox (0,t0) (1/512) (1/512))
    (y : Fin 4 → ℂ) (t : Fin 3 → ℂ)
    (hy : (7*physicalKSPointwiseRate M A)*‖y‖<1)
    (ht : (7*physicalKSPointwiseRate M A)*‖t‖<1) :
    HasSum (fun k : ℕ × (Fin 3 → ℕ) =>
      eval y (physicalKSTaylorSpectatorFamily f x k.1 k.2) * ∏ i : Fin 3, t i ^ k.2 i)
      (physicalKSComplexTaylorExtension f x (Sum.elim y t)) := by
  have hs := (physicalKSTaylorSpectatorFamily_summable hdata hA hF0 hx y t hy ht).2
  have he := groupedHomogeneousSpectatorPolynomial_tsum_eq
    (physicalKSTaylorSpectatorFamily f x) y t hs
  simp only [physicalKSTaylorSpectatorFamily_grouped] at he
  change physicalKSComplexTaylorExtension f x (Sum.elim y t) = _ at he
  rw [he]
  exact hs.hasSum

theorem physicalKSTaylorSpectatorFamily_hasSum_real_ball
    {f : Space (Fin 3) → ℂ} {t0 : Position} {M A F0 W : ℝ}
    (hdata : PhysicalKSBoxPointwiseData f t0 M A F0 W)
    (hA : 1≤A) (hF0 : 0≤F0) :
    ∃ r : ℝ≥0, 0<r ∧ (r : ℝ)=min (1/1024) (7*physicalKSPointwiseRate M A)⁻¹ ∧
      ∀ x ∈ rectangularClosedBox (0,t0) (1/1024) (1/1024),
        ∀ q ∈ Metric.eball (0 : Space (Fin 3)) (r : ℝ≥0∞),
          HasSum (fun k : ℕ × (Fin 3 → ℕ) =>
            eval (fun i => (q.1 i : ℂ)) (physicalKSTaylorSpectatorFamily f x k.1 k.2) *
              ∏ i : Fin 3, (q.2 i : ℂ) ^ k.2 i) (f (x+q)) := by
  obtain ⟨r,hr,he,hreal⟩ := physicalKSComplexTaylorExtension_agrees_on_real_ball hdata hA hF0
  refine ⟨r,hr,he,?_⟩
  intro x hx q hq
  have hx' : x ∈ rectangularOpenBox (0,t0) (1/512) (1/512) := by
    apply physical_fixed_box_ball_room (0,t0) x hx
    simp
  have hnorm : ‖q‖ < (r : ℝ) := by
    simpa only [Metric.eball_coe,Metric.mem_ball,dist_zero_right] using hq
  have hS : 0 < 7*physicalKSPointwiseRate M A :=
    mul_pos (by norm_num) (physicalKSPointwiseRate_pos hA)
  have hsmall : (7*physicalKSPointwiseRate M A)*‖q‖<1 := by
    have hlt : ‖q‖ < (7*physicalKSPointwiseRate M A)⁻¹ :=
      hnorm.trans_le (he ▸ min_le_right _ _)
    calc
      _ < (7*physicalKSPointwiseRate M A)*(7*physicalKSPointwiseRate M A)⁻¹ :=
        mul_lt_mul_of_pos_left hlt hS
      _ = 1 := mul_inv_cancel₀ hS.ne'
  have hy : ‖(fun i : Fin 4 => (q.1 i : ℂ))‖ ≤ ‖q‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
    intro i
    simpa only [Complex.norm_real,Real.norm_eq_abs,productCoordinateComponent] using
      productCoordinateComponent_abs_le q (Sum.inl i)
  have ht : ‖(fun i : Fin 3 => (q.2 i : ℂ))‖ ≤ ‖q‖ := by
    apply (pi_norm_le_iff_of_nonneg (norm_nonneg q)).mpr
    intro i
    simpa only [Complex.norm_real,Real.norm_eq_abs,productCoordinateComponent] using
      productCoordinateComponent_abs_le q (Sum.inr i)
  have hs := physicalKSTaylorSpectatorFamily_hasSum_complex hdata hA hF0 hx'
    (fun i => (q.1 i : ℂ)) (fun i => (q.2 i : ℂ))
    ((mul_le_mul_of_nonneg_left hy hS.le).trans_lt hsmall)
    ((mul_le_mul_of_nonneg_left ht hS.le).trans_lt hsmall)
  have hcoord : Sum.elim (fun i : Fin 4 => (q.1 i : ℂ)) (fun i : Fin 3 => (q.2 i : ℂ)) =
      (fun j => (productCoordinateComponent q j : ℂ)) := by
    funext j
    cases j <;> rfl
  rw [hcoord,hreal x hx q hq] at hs
  exact hs

end TheoremT.Continuum
