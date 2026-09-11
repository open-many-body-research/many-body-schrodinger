import HydrogenAngularGreen_v1

/-! Summed Green identity and exact cancellation of derivatives of a radial
cutoff against the tangential derivative of an actual angular extension. -/
noncomputable section
open MeasureTheory
open scoped ContDiff Topology BigOperators
namespace TheoremT.HydrogenPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem sum_coordinate_partial_radial (f : EuclideanSpace ℝ σ → ℝ)
    (x : EuclideanSpace ℝ σ) :
    (∑ i : σ, x i * euclideanPartial i f x) = fderiv ℝ f x x := by
  have he : (∑ i : σ, x i • EuclideanSpace.single i (1 : ℝ)) = x := by
    ext j
    simp [Pi.single_apply, mul_ite]
  have h := congrArg (fderiv ℝ f x) he
  simpa [euclideanPartial] using h

theorem squaredRadiusCutoff_partial {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (i : σ) (x : EuclideanSpace ℝ σ) :
    euclideanPartial i (fun y : EuclideanSpace ℝ σ => η (‖y‖ ^ 2)) x =
      2 * deriv η (‖x‖ ^ 2) * x i := by
  have hη' := ((hη.differentiable (by simp)) (‖x‖ ^ 2)).hasDerivAt
  have hh := hη'.comp_hasFDerivAt x (hasStrictFDerivAt_norm_sq x).hasFDerivAt
  change HasFDerivAt (fun y : EuclideanSpace ℝ σ => η (‖y‖ ^ 2)) _ x at hh
  dsimp [euclideanPartial]
  rw [hh.fderiv]
  simp [EuclideanSpace.inner_single_right]
  ring

theorem squaredRadiusCutoff_angular_cross_zero {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    {P : MvPolynomial (Fin 3) ℝ} {m : ℕ} (hP : P.IsHomogeneous m)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    (∑ i : Fin 3, euclideanPartial i (fun y : EuclideanSpace ℝ (Fin 3) => η (‖y‖ ^ 2)) x *
      euclideanPartial i (harmonicAngularExtension m P) x) = 0 := by
  simp_rw [squaredRadiusCutoff_partial hη]
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [sum_coordinate_partial_radial, harmonicAngularExtension_radial_zero hP hx, mul_zero]
  simp

theorem punctured_cutoff_green_sum {χ u v : EuclideanSpace ℝ σ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport χ)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ u x)
    (hv : ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ v x) :
    (∫ x, χ x * u x * ∑ i : σ, euclideanPartial i (euclideanPartial i v) x) =
      -(∑ i : σ, ∫ x, χ x * (euclideanPartial i u x * euclideanPartial i v x)) -
        (∫ x, u x * ∑ i : σ, euclideanPartial i χ x * euclideanPartial i v x) := by
  have hleft (i : σ) : Integrable (fun x => χ x * u x *
      euclideanPartial i (euclideanPartial i v) x) := by
    have hi := cutoff_mul_integrable_of_away_zero hχ hχc hχ0
      (fun x hx => (hu x hx).mul
        (partial_contDiff_away_zero (partial_contDiff_away_zero hv i) i x hx))
    simpa only [mul_assoc] using hi
  have hright (i : σ) : Integrable (fun x => euclideanPartial i χ x *
      (u x * euclideanPartial i v x)) := by
    apply cutoff_mul_integrable_of_away_zero (partial_contDiff hχ i) (hχc.fderiv_apply ℝ _)
      (fun h => hχ0 (tsupport_fderiv_apply_subset ℝ _ h))
    intro x hx
    exact (hu x hx).mul (partial_contDiff_away_zero hv i x hx)
  calc
    _ = ∑ i : σ, ∫ x, χ x * u x * euclideanPartial i (euclideanPartial i v) x := by
      simp_rw [Finset.mul_sum]
      exact integral_finsetSum _ (fun i _ => hleft i)
    _ = -(∑ i : σ, ∫ x, χ x * (euclideanPartial i u x * euclideanPartial i v x)) -
        (∑ i : σ, ∫ x, euclideanPartial i χ x * (u x * euclideanPartial i v x)) := by
      simp_rw [punctured_cutoff_green_coordinate hχ hχc hχ0 hu hv,
        Finset.sum_sub_distrib, Finset.sum_neg_distrib]
    _ = _ := by
      congr 1
      rw [← integral_finsetSum _ (fun i _ => hright i)]
      congr 1
      funext x
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring

end TheoremT.HydrogenPolynomial
