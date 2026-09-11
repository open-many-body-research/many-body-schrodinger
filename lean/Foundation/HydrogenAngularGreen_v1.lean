import HydrogenAngularRegularity_v1

/-! A cutoff Green identity on punctured Euclidean space. All integrability
and support obligations are derived from actual smoothness and compact support.
This is the Euclidean integration step underlying the angular energy identity. -/
noncomputable section
open MeasureTheory
open scoped ContDiff Topology BigOperators
namespace TheoremT.HydrogenPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def euclideanPartial (i : σ) (f : EuclideanSpace ℝ σ → ℝ) (x : EuclideanSpace ℝ σ) : ℝ :=
  fderiv ℝ f x (EuclideanSpace.single i 1)

theorem partial_contDiff_away_zero {f : EuclideanSpace ℝ σ → ℝ}
    (hf : ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ f x) (i : σ) :
    ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ (euclideanPartial i f) x := by
  intro x hx
  exact ((hf x hx).fderiv_right (by simp)).clm_apply contDiffAt_const

theorem partial_contDiff {f : EuclideanSpace ℝ σ → ℝ}
    (hf : ContDiff ℝ ∞ f) (i : σ) : ContDiff ℝ ∞ (euclideanPartial i f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  exact (hf.contDiffAt.fderiv_right (by simp)).clm_apply contDiffAt_const

theorem cutoff_mul_partial {χ u : EuclideanSpace ℝ σ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχ0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport χ)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ u x) (i : σ) (x : EuclideanSpace ℝ σ) :
    euclideanPartial i (fun y => χ y * u y) x =
      χ x * euclideanPartial i u x + euclideanPartial i χ x * u x := by
  by_cases hx : x = 0
  · subst x
    have hf0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport (fun y => χ y * u y) :=
      fun h => hχ0 (tsupport_mul_subset_left h)
    simp [euclideanPartial, fderiv_of_notMem_tsupport ℝ hf0,
      fderiv_of_notMem_tsupport ℝ hχ0, image_eq_zero_of_notMem_tsupport hχ0]
  · dsimp [euclideanPartial]
    rw [fderiv_fun_mul (hχ.differentiable (by simp) x) ((hu x hx).differentiableAt (by simp))]
    simp
    ring

theorem punctured_cutoff_green_coordinate {χ u v : EuclideanSpace ℝ σ → ℝ}
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ)
    (hχ0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport χ)
    (hu : ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ u x)
    (hv : ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ v x) (i : σ) :
    (∫ x, χ x * u x * euclideanPartial i (euclideanPartial i v) x) =
      -(∫ x, χ x * (euclideanPartial i u x * euclideanPartial i v x)) -
        (∫ x, euclideanPartial i χ x * (u x * euclideanPartial i v x)) := by
  let f := fun x => χ x * u x
  have hf : ContDiff ℝ ∞ f := cutoff_mul_contDiff_of_away_zero hχ hχ0 hu
  have hfc : HasCompactSupport f := hχc.mul_right
  have hf0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport f :=
    fun h => hχ0 (tsupport_mul_subset_left h)
  have hfi : ContDiff ℝ ∞ (euclideanPartial i f) := partial_contDiff hf i
  have hfic : HasCompactSupport (euclideanPartial i f) := hfc.fderiv_apply ℝ _
  have hfi0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport (euclideanPartial i f) :=
    fun h => hf0 (tsupport_fderiv_apply_subset ℝ _ h)
  have hvi := partial_contDiff_away_zero hv i
  have hvii := partial_contDiff_away_zero hvi i
  have hfg := cutoff_mul_integrable_of_away_zero hf hfc hf0 hvi
  have hfg' := cutoff_mul_integrable_of_away_zero hf hfc hf0 hvii
  have hf'g := cutoff_mul_integrable_of_away_zero hfi hfic hfi0 hvi
  have hb := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable hf'g hfg' hfg
    (fun x _ => hf.differentiable (by simp) x)
    (fun x hx => (hvi x (fun h => hf0 (h ▸ hx))).differentiableAt (by simp))
  have hχi := partial_contDiff hχ i
  have hχic : HasCompactSupport (euclideanPartial i χ) := hχc.fderiv_apply ℝ _
  have hχi0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport (euclideanPartial i χ) :=
    fun h => hχ0 (tsupport_fderiv_apply_subset ℝ _ h)
  have hfirst := cutoff_mul_integrable_of_away_zero hχ hχc hχ0
    (fun x hx => (partial_contDiff_away_zero hu i x hx).mul (hvi x hx))
  have hsecond := cutoff_mul_integrable_of_away_zero hχi hχic hχi0
    (fun x hx => (hu x hx).mul (hvi x hx))
  change (∫ x, f x * euclideanPartial i (euclideanPartial i v) x) =
    -(∫ x, euclideanPartial i f x * euclideanPartial i v x) at hb
  rw [show (fun x => euclideanPartial i f x * euclideanPartial i v x) =
      (fun x => χ x * (euclideanPartial i u x * euclideanPartial i v x) +
        euclideanPartial i χ x * (u x * euclideanPartial i v x)) by
      funext x
      dsimp [f]
      rw [cutoff_mul_partial hχ hχ0 hu]
      ring,
    integral_add hfirst hsecond] at hb
  simpa only [f, neg_add_rev, sub_eq_add_neg, add_comm] using hb

end TheoremT.HydrogenPolynomial
