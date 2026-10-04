import GrushinCutoffWeightedL2Removal_v1

/-! Actual weighted L2 localization for the spatial first-order term in
the factorial commutator, with the derivative-support premise discharged
by the explicit centered cutoff. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_y_first_weighted_L2 (a : Space (Fin 3)) (ha : a.1 = 0)
    {aY aT ρ s e C1 C2 : ℝ} (he : 0 < e) (hse : s+e ≤ ρ) (hρ : ρ < aY)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    {μ : Measure (Space (Fin 3))} {f : Space (Fin 3) → ℂ}
    (hf : AEStronglyMeasurable f μ) (i : Fin 4) (w : Fin 4 → Lp ℂ 2 μ)
    (hw : ∀ l, w l =ᵐ[μ] (fun p => (p.1 l)^2 • f p)) :
    ∃ u : Lp ℂ 2 μ,
      u =ᵐ[μ] (fun p => fderiv ℝ (factorialRectCutoff a aY aT s e) p (yDir i) • f p) ∧
      ‖u‖ ≤ (((8/3 : ℝ)*C1)/e)/(aY-ρ)^2*(∑ l, ‖w l‖) := by
  have hχ : ContDiff ℝ ∞ (factorialRectCutoff a aY aT s e) :=
    grushinRectCutoff_contDiff a _ _ _
  have hd : Continuous (fun p => fderiv ℝ (factorialRectCutoff a aY aT s e) p (yDir i)) :=
    ((hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
  obtain ⟨hb,_⟩ := factorialRectCutoff_derivative_bounds a aY aT s he hC1 hC2
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  apply cutoff_weight_removal_L2 hf hd.aestronglyMeasurable (sub_pos.mpr hρ)
    (by positivity : 0 ≤ ((8/3 : ℝ)*C1)/e) (Filter.Eventually.of_forall (hb (.inl i)))
    _ w hw
  exact Filter.Eventually.of_forall (fun p hp =>
    factorialRectCutoff_y_lower_radius a ha he hse i (Or.inl (subset_tsupport _ hp)))

theorem factorial_y_second_weighted_L2 (a : Space (Fin 3)) (ha : a.1 = 0)
    {aY aT ρ s e C1 C2 : ℝ} (he : 0 < e) (hse : s+e ≤ ρ) (hρ : ρ < aY)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    {μ : Measure (Space (Fin 3))} {f : Space (Fin 3) → ℂ}
    (hf : AEStronglyMeasurable f μ) (i : Fin 4) (w : Fin 4 → Lp ℂ 2 μ)
    (hw : ∀ l, w l =ᵐ[μ] (fun p => (p.1 l)^2 • f p)) :
    ∃ u : Lp ℂ 2 μ,
      u =ᵐ[μ] (fun p => fderiv ℝ
        (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (yDir i)) p (yDir i) • f p) ∧
      ‖u‖ ≤ (((32/9 : ℝ)*(C2+C1^2))/e^2)/(aY-ρ)^2*(∑ l, ‖w l‖) := by
  have hχ : ContDiff ℝ ∞ (factorialRectCutoff a aY aT s e) :=
    grushinRectCutoff_contDiff a _ _ _
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ (factorialRectCutoff a aY aT s e) p (yDir i)) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hdd : Continuous (fun p => fderiv ℝ
      (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (yDir i)) p (yDir i)) :=
    ((hd.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
  obtain ⟨_,hb⟩ := factorialRectCutoff_derivative_bounds a aY aT s he hC1 hC2
  have hC20 : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  apply cutoff_weight_removal_L2 hf hdd.aestronglyMeasurable (sub_pos.mpr hρ)
    (by positivity : 0 ≤ ((32/9 : ℝ)*(C2+C1^2))/e^2)
    (Filter.Eventually.of_forall (hb (.inl i))) _ w hw
  exact Filter.Eventually.of_forall (fun p hp =>
    factorialRectCutoff_y_lower_radius a ha he hse i (Or.inr (subset_tsupport _ hp)))

end TheoremT.Continuum.WeakGrushin
