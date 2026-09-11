import HydrogenAngularExtension_v1
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! The angular extensions are genuinely smooth off the origin. Multiplying
by a smooth cutoff whose closed support avoids the origin gives globally smooth
functions; no differentiability at the removed singularity is presumed. -/
noncomputable section
open MeasureTheory
open scoped ContDiff Topology BigOperators
namespace TheoremT.HydrogenPolynomial

variable {σ : Type*} [Fintype σ] [DecidableEq σ]

theorem radialSquaredPower_contDiffAt (a : ℝ) {x : EuclideanSpace ℝ σ}
    (hx : x ≠ 0) : ContDiffAt ℝ ∞ (radialSquaredPower a) x := by
  exact (contDiff_norm_sq ℝ).contDiffAt.rpow_const_of_ne
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hx))

theorem harmonicAngularExtension_contDiffAt (m : ℕ)
    (P : MvPolynomial (Fin 3) ℝ) {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (harmonicAngularExtension m P) x :=
  (radialSquaredPower_contDiffAt _ hx).mul (euclideanEvaluation_contDiff P).contDiffAt

theorem cutoff_mul_contDiff_of_away_zero {f g : EuclideanSpace ℝ σ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hf0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport f)
    (hg : ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ g x) :
    ContDiff ℝ ∞ (fun x => f x * g x) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : EuclideanSpace ℝ σ => (0 : ℝ)) 0).congr_of_eventuallyEq
    filter_upwards [(isClosed_tsupport f).isOpen_compl.mem_nhds hf0] with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  · exact hf.contDiffAt.mul (hg x hx)

theorem cutoff_mul_integrable_of_away_zero {f g : EuclideanSpace ℝ σ → ℝ}
    (hf : ContDiff ℝ ∞ f) (hfc : HasCompactSupport f)
    (hf0 : (0 : EuclideanSpace ℝ σ) ∉ tsupport f)
    (hg : ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ g x) :
    Integrable (fun x => f x * g x) := by
  exact (cutoff_mul_contDiff_of_away_zero hf hf0 hg).continuous.integrable_of_hasCompactSupport hfc.mul_right

theorem angularExtension_partial_contDiffAt (m : ℕ)
    (P : MvPolynomial (Fin 3) ℝ) (i : Fin 3)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => fderiv ℝ (harmonicAngularExtension m P) y
      (EuclideanSpace.single i 1)) x :=
  ((harmonicAngularExtension_contDiffAt m P hx).fderiv_right (by simp)).clm_apply contDiffAt_const

theorem angularExtension_second_partial_contDiffAt (m : ℕ)
    (P : MvPolynomial (Fin 3) ℝ) (i j : Fin 3)
    {x : EuclideanSpace ℝ (Fin 3)} (hx : x ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => fderiv ℝ
      (fun z => fderiv ℝ (harmonicAngularExtension m P) z (EuclideanSpace.single i 1))
      y (EuclideanSpace.single j 1)) x :=
  ((angularExtension_partial_contDiffAt m P i hx).fderiv_right (by simp)).clm_apply contDiffAt_const

theorem angularExtension_cutoff_partial_integrable (m l : ℕ)
    (P Q : MvPolynomial (Fin 3) ℝ) (i j : Fin 3)
    {χ : EuclideanSpace ℝ (Fin 3) → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hχc : HasCompactSupport χ) (hχ0 : (0 : EuclideanSpace ℝ (Fin 3)) ∉ tsupport χ) :
    Integrable (fun x => χ x *
      (fderiv ℝ (harmonicAngularExtension l Q) x (EuclideanSpace.single i 1) *
       fderiv ℝ (harmonicAngularExtension m P) x (EuclideanSpace.single j 1))) := by
  apply cutoff_mul_integrable_of_away_zero hχ hχc hχ0
  intro x hx
  exact (angularExtension_partial_contDiffAt l Q i hx).mul
    (angularExtension_partial_contDiffAt m P j hx)

end TheoremT.HydrogenPolynomial
