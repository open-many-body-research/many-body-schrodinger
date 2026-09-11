import CompactHessianCross_v1

noncomputable section
open MeasureTheory
open scoped ContDiff RealInnerProductSpace BigOperators
namespace TheoremT.Continuum
variable {E F ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [Fintype ι]
  {μ : Measure E} [μ.IsAddHaarMeasure]

theorem compact_finite_hessian_identity {u : E → F}
    (hu : ContDiff ℝ ∞ u) (hc : HasCompactSupport u) (v : ι → E) :
    (∫ x, ‖∑ i : ι,fderiv ℝ (fun y => fderiv ℝ u y (v i)) x (v i)‖^2 ∂μ) =
      ∑ i : ι,∑ j : ι,∫ x, ‖fderiv ℝ (fun y => fderiv ℝ u y (v i)) x (v j)‖^2 ∂μ := by
  have hd (q : E) : ContDiff ℝ ∞ (fun x => fderiv ℝ u x q) :=
    (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hdd (q r : E) : ContDiff ℝ ∞ (fun x => fderiv ℝ (fun y => fderiv ℝ u y q) x r) :=
    ((hd q).fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hi (i j : ι) := compact_real_inner_integrable_general (μ := μ)
    (hdd (v i) (v i)).continuous (hdd (v j) (v j)).continuous
    ((hc.fderiv_apply ℝ (v i)).fderiv_apply ℝ (v i))
  have he (x : E) : ‖∑ i : ι,fderiv ℝ (fun y => fderiv ℝ u y (v i)) x (v i)‖^2 =
      ∑ i : ι,∑ j : ι,inner ℝ (fderiv ℝ (fun y => fderiv ℝ u y (v i)) x (v i))
        (fderiv ℝ (fun y => fderiv ℝ u y (v j)) x (v j)) := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [sum_inner,inner_sum]
    exact Finset.sum_comm
  simp_rw [he]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hi i j))]
  simp_rw [integral_finsetSum _ (fun j _ => hi _ j)]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact compact_second_directional_cross hu hc (v i) (v j)

#print axioms compact_finite_hessian_identity
end TheoremT.Continuum
