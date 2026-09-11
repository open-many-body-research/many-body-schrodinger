import HydrogenAngularPolar_v1

/-! Bilinearity of the actual sphere integrals on functions smooth away from
the origin. Compactness of the geometric sphere supplies integrability. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenPolynomial

def SmoothAwayZero (f : AngularR3 → ℝ) : Prop :=
  ∀ x, x ≠ 0 → ContDiffAt ℝ ∞ f x

theorem smoothAwayZero_sphere_continuous {f : AngularR3 → ℝ} (hf : SmoothAwayZero f) :
    Continuous (fun w : Metric.sphere (0 : AngularR3) 1 => f w.val) := by
  rw [continuous_iff_continuousAt]
  intro w
  have hw : w.val ≠ 0 := by
    intro he
    simpa [he, Metric.mem_sphere] using w.property
  exact (hf w.val hw).continuousAt.comp continuous_subtype_val.continuousAt

theorem smoothAwayZero_sphere_integrable_mul {f g : AngularR3 → ℝ}
    (hf : SmoothAwayZero f) (hg : SmoothAwayZero g) :
    Integrable (fun w : Metric.sphere (0 : AngularR3) 1 => f w.val * g w.val)
      (volume : Measure AngularR3).toSphere :=
  ((smoothAwayZero_sphere_continuous hf).mul (smoothAwayZero_sphere_continuous hg)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem smoothAwayZero_partial {f : AngularR3 → ℝ} (hf : SmoothAwayZero f) (i : Fin 3) :
    SmoothAwayZero (euclideanPartial i f) := partial_contDiff_away_zero hf i

theorem smoothAwayZero_sum {ι : Type*} (s : Finset ι) (f : ι → AngularR3 → ℝ)
    (hf : ∀ j ∈ s, SmoothAwayZero (f j)) : SmoothAwayZero (fun x => ∑ j ∈ s, f j x) := by
  intro x hx
  exact ContDiffAt.sum (fun j hj => hf j hj x hx)

theorem euclideanPartial_sum {ι : Type*} (s : Finset ι) (f : ι → AngularR3 → ℝ)
    (hf : ∀ j ∈ s, SmoothAwayZero (f j)) {x : AngularR3} (hx : x ≠ 0) (i : Fin 3) :
    euclideanPartial i (fun y => ∑ j ∈ s, f j y) x = ∑ j ∈ s, euclideanPartial i (f j) x := by
  dsimp [euclideanPartial]
  rw [fderiv_fun_sum (fun j hj => (hf j hj x hx).differentiableAt (by simp))]
  simp

theorem sphereAngularInner_sum_left {ι : Type*} (s : Finset ι) (f : ι → AngularR3 → ℝ)
    {g : AngularR3 → ℝ} (hf : ∀ j ∈ s, SmoothAwayZero (f j)) (hg : SmoothAwayZero g) :
    sphereAngularInner (fun x => ∑ j ∈ s, f j x) g = ∑ j ∈ s, sphereAngularInner (f j) g := by
  unfold sphereAngularInner
  simp_rw [Finset.sum_mul]
  exact integral_finsetSum s (fun j hj => smoothAwayZero_sphere_integrable_mul (hf j hj) hg)

theorem sphereAngularInner_comm (f g : AngularR3 → ℝ) :
    sphereAngularInner f g = sphereAngularInner g f := by
  simp [sphereAngularInner, mul_comm]

theorem sphereAngularInner_sum_right {ι : Type*} (s : Finset ι) (f : ι → AngularR3 → ℝ)
    {g : AngularR3 → ℝ} (hf : ∀ j ∈ s, SmoothAwayZero (f j)) (hg : SmoothAwayZero g) :
    sphereAngularInner g (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, sphereAngularInner g (f j) := by
  rw [sphereAngularInner_comm, sphereAngularInner_sum_left s f hf hg]
  apply Finset.sum_congr rfl
  intro j _
  exact sphereAngularInner_comm _ _

theorem sphereAngularEnergy_sum_left {ι : Type*} (s : Finset ι) (f : ι → AngularR3 → ℝ)
    {g : AngularR3 → ℝ} (hf : ∀ j ∈ s, SmoothAwayZero (f j)) (hg : SmoothAwayZero g) :
    sphereAngularEnergy (fun x => ∑ j ∈ s, f j x) g = ∑ j ∈ s, sphereAngularEnergy (f j) g := by
  unfold sphereAngularEnergy
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  calc
    _ = ∫ w : Metric.sphere (0 : AngularR3) 1,
      (∑ j ∈ s, euclideanPartial i (f j) w.val) * euclideanPartial i g w.val
        ∂(volume : Measure AngularR3).toSphere := by
      apply integral_congr_ae
      apply Filter.Eventually.of_forall
      intro w
      dsimp only
      have hw : w.val ≠ 0 := by intro he; simpa [he, Metric.mem_sphere] using w.property
      rw [euclideanPartial_sum s f hf hw]
    _ = _ := by
      simp_rw [Finset.sum_mul]
      exact integral_finsetSum s (fun j hj => smoothAwayZero_sphere_integrable_mul
        (smoothAwayZero_partial (hf j hj) i) (smoothAwayZero_partial hg i))

theorem sphereAngularEnergy_comm (f g : AngularR3 → ℝ) :
    sphereAngularEnergy f g = sphereAngularEnergy g f := by
  simp [sphereAngularEnergy, mul_comm]

theorem sphereAngularEnergy_sum_right {ι : Type*} (s : Finset ι) (f : ι → AngularR3 → ℝ)
    {g : AngularR3 → ℝ} (hf : ∀ j ∈ s, SmoothAwayZero (f j)) (hg : SmoothAwayZero g) :
    sphereAngularEnergy g (fun x => ∑ j ∈ s, f j x) = ∑ j ∈ s, sphereAngularEnergy g (f j) := by
  rw [sphereAngularEnergy_comm, sphereAngularEnergy_sum_left s f hf hg]
  apply Finset.sum_congr rfl
  intro j _
  exact sphereAngularEnergy_comm _ _

theorem sphereAngularInner_self_nonneg (f : AngularR3 → ℝ) : 0 ≤ sphereAngularInner f f := by
  exact integral_nonneg (fun w => mul_self_nonneg (f w.val))

end TheoremT.HydrogenPolynomial
