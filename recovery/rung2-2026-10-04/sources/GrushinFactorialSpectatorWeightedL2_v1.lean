import GrushinRadialWeightedL2Multiplier_v1

/-! Actual spectator first- and second-cutoff terms of the factorial
commutator, retaining the operator's radial-square factor. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators ContDiff
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_t_first_weighted_L2 (a : Space (Fin 3)) (aY aT s c : ℝ)
    {e C1 C2 : ℝ} (he : 0 < e)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    {μ : Measure (Space (Fin 3))} {f : Space (Fin 3) → ℂ}
    (j : Fin 3) (w : Fin 4 → Lp ℂ 2 μ)
    (hw : ∀ l, w l =ᵐ[μ] (fun p => (p.1 l)^2 • f p)) :
    ∃ u : Lp ℂ 2 μ,
      u =ᵐ[μ] (fun p => (c*‖p.1‖^2) •
        (fderiv ℝ (factorialRectCutoff a aY aT s e) p (tDir j) • f p)) ∧
      ‖u‖ ≤ (|c| * (((8/3 : ℝ)*C1)/e))*(∑ l, ‖w l‖) := by
  have hχ : ContDiff ℝ ∞ (factorialRectCutoff a aY aT s e) :=
    grushinRectCutoff_contDiff a _ _ _
  have hd : Continuous (fun p => fderiv ℝ (factorialRectCutoff a aY aT s e) p (tDir j)) :=
    ((hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
  obtain ⟨hb,_⟩ := factorialRectCutoff_derivative_bounds a aY aT s he hC1 hC2
  have hC10 : 0 ≤ C1 := (abs_nonneg _).trans (hC1 0)
  have ha : ∀ᵐ p ∂μ, |c*fderiv ℝ (factorialRectCutoff a aY aT s e) p (tDir j)| ≤
      |c| * (((8/3 : ℝ)*C1)/e) := by
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb (.inr j) p) (abs_nonneg c)
  obtain ⟨u,hu,hn⟩ := radial_weight_bounded_multiplier_L2
    (hd.const_mul c).aestronglyMeasurable (by positivity) ha w hw
  refine ⟨u,?_,hn⟩
  filter_upwards [hu] with p hp
  rw [hp,smul_smul,smul_smul]
  congr 1
  ring

theorem factorial_t_second_weighted_L2 (a : Space (Fin 3)) (aY aT s c : ℝ)
    {e C1 C2 : ℝ} (he : 0 < e)
    (hC1 : ∀ x, |deriv Real.smoothTransition x| ≤ C1)
    (hC2 : ∀ x, |deriv (deriv Real.smoothTransition) x| ≤ C2)
    {μ : Measure (Space (Fin 3))} {f : Space (Fin 3) → ℂ}
    (j : Fin 3) (w : Fin 4 → Lp ℂ 2 μ)
    (hw : ∀ l, w l =ᵐ[μ] (fun p => (p.1 l)^2 • f p)) :
    ∃ u : Lp ℂ 2 μ,
      u =ᵐ[μ] (fun p => (c*‖p.1‖^2) •
        (fderiv ℝ (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (tDir j)) p
          (tDir j) • f p)) ∧
      ‖u‖ ≤ (|c| * (((32/9 : ℝ)*(C2+C1^2))/e^2))*(∑ l, ‖w l‖) := by
  have hχ : ContDiff ℝ ∞ (factorialRectCutoff a aY aT s e) :=
    grushinRectCutoff_contDiff a _ _ _
  have hd : ContDiff ℝ ∞ (fun p => fderiv ℝ (factorialRectCutoff a aY aT s e) p (tDir j)) :=
    (hχ.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const
  have hdd : Continuous (fun p => fderiv ℝ
      (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (tDir j)) p (tDir j)) :=
    ((hd.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiff_const).continuous
  obtain ⟨_,hb⟩ := factorialRectCutoff_derivative_bounds a aY aT s he hC1 hC2
  have hC20 : 0 ≤ C2 := (abs_nonneg _).trans (hC2 0)
  have ha : ∀ᵐ p ∂μ, |c*fderiv ℝ
      (fun q => fderiv ℝ (factorialRectCutoff a aY aT s e) q (tDir j)) p (tDir j)| ≤
      |c| * (((32/9 : ℝ)*(C2+C1^2))/e^2) := by
    apply Filter.Eventually.of_forall
    intro p
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (hb (.inr j) p) (abs_nonneg c)
  obtain ⟨u,hu,hn⟩ := radial_weight_bounded_multiplier_L2
    (hdd.const_mul c).aestronglyMeasurable (by positivity) ha w hw
  refine ⟨u,?_,hn⟩
  filter_upwards [hu] with p hp
  rw [hp,smul_smul,smul_smul]
  congr 1
  ring

end TheoremT.Continuum.WeakGrushin
