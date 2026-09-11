import HydrogenAngularWeightedIdentity_v1
import HydrogenAngularDerivativeScaling_v1
import PolarThree_v1

/-! Transfer of the actual annular Euclidean identities to the genuine unit
sphere area measure by the proved full nonradial polar formula. -/
noncomputable section
open MeasureTheory Set
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenPolynomial

def sphereAngularInner (u v : AngularR3 → ℝ) : ℝ :=
  ∫ w : Metric.sphere (0 : AngularR3) 1, u w.val * v w.val ∂(volume : Measure AngularR3).toSphere

def sphereAngularEnergy (u v : AngularR3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∫ w : Metric.sphere (0 : AngularR3) 1,
    euclideanPartial i u w.val * euclideanPartial i v w.val ∂(volume : Measure AngularR3).toSphere

def radialCutoffIntegral (η : ℝ → ℝ) : ℝ := ∫ r : ℝ in Ioi 0, η (r ^ 2)

theorem weightedAngularInner_polar {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hη0 : (0 : AngularR3) ∉ tsupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    {P Q : MvPolynomial (Fin 3) ℝ} {m l : ℕ}
    (hP : P.IsHomogeneous m) (hQ : Q.IsHomogeneous l) :
    weightedAngularInner η (harmonicAngularExtension l Q) (harmonicAngularExtension m P) =
      radialCutoffIntegral η *
        sphereAngularInner (harmonicAngularExtension l Q) (harmonicAngularExtension m P) := by
  let u := harmonicAngularExtension l Q
  let v := harmonicAngularExtension m P
  have hχ : ContDiff ℝ ∞ (fun x : AngularR3 => η (‖x‖ ^ 2)) := hη.comp (contDiff_norm_sq ℝ)
  have hi : Integrable (fun x : AngularR3 => η (‖x‖ ^ 2) / ‖x‖ ^ 2 * u x * v x) := by
    have h := cutoff_mul_integrable_of_away_zero hχ hηc hη0
      (fun x hx => (radialSquaredPower_contDiffAt (-1) hx).mul
        ((harmonicAngularExtension_contDiffAt l Q hx).mul
          (harmonicAngularExtension_contDiffAt m P hx)))
    convert h using 1
    funext x
    simp [radialSquaredPower, Real.rpow_neg_one, div_eq_mul_inv, mul_assoc, u, v]
  rw [weightedAngularInner, TheoremT.Polar.integral_polar_dim_three_sphere_outer
    (by simp : Module.finrank ℝ AngularR3 = 3) _ hi]
  change (∫ w : Metric.sphere (0 : AngularR3) 1,
    (∫ r : ℝ in Ioi 0, r ^ 2 • (η (‖r • w.val‖ ^ 2) / ‖r • w.val‖ ^ 2 * u (r • w.val) *
      v (r • w.val))) ∂(volume : Measure AngularR3).toSphere) = _
  have he (w : Metric.sphere (0 : AngularR3) 1) :
      (∫ r : ℝ in Ioi 0, r ^ 2 • (η (‖r • w.val‖ ^ 2) / ‖r • w.val‖ ^ 2 * u (r • w.val) *
        v (r • w.val))) = radialCutoffIntegral η * (u w.val * v w.val) := by
    rw [radialCutoffIntegral, ← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    dsimp only
    have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
    have hsU := harmonicAngularExtension_scale hQ hr w.val
    have hsV := harmonicAngularExtension_scale hP hr w.val
    change u (r • w.val) = u w.val at hsU
    change v (r • w.val) = v w.val at hsV
    rw [hsU, hsV, norm_smul, Real.norm_eq_abs, abs_of_pos hr, hw, mul_one]
    try simp only [smul_eq_mul]
    field_simp [(show 0 < r from hr).ne']
  simp_rw [he]
  rw [integral_const_mul]
  rfl

theorem weightedAngularEnergy_polar {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hη0 : (0 : AngularR3) ∉ tsupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    {P Q : MvPolynomial (Fin 3) ℝ} {m l : ℕ}
    (hP : P.IsHomogeneous m) (hQ : Q.IsHomogeneous l) :
    weightedAngularEnergy η (harmonicAngularExtension l Q) (harmonicAngularExtension m P) =
      radialCutoffIntegral η *
        sphereAngularEnergy (harmonicAngularExtension l Q) (harmonicAngularExtension m P) := by
  let u := harmonicAngularExtension l Q
  let v := harmonicAngularExtension m P
  unfold weightedAngularEnergy sphereAngularEnergy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := angularExtension_cutoff_partial_integrable m l P Q i i
    (hη.comp (contDiff_norm_sq ℝ)) hηc hη0
  change Integrable (fun x : AngularR3 => η (‖x‖ ^ 2) *
    (euclideanPartial i (harmonicAngularExtension l Q) x *
      euclideanPartial i (harmonicAngularExtension m P) x)) at hi
  rw [TheoremT.Polar.integral_polar_dim_three_sphere_outer
    (by simp : Module.finrank ℝ AngularR3 = 3) _ hi]
  change (∫ w : Metric.sphere (0 : AngularR3) 1,
    (∫ r : ℝ in Ioi 0, r ^ 2 • (η (‖r • w.val‖ ^ 2) *
      (euclideanPartial i u (r • w.val) * euclideanPartial i v (r • w.val))))
        ∂(volume : Measure AngularR3).toSphere) = _
  have he (w : Metric.sphere (0 : AngularR3) 1) :
      (∫ r : ℝ in Ioi 0, r ^ 2 • (η (‖r • w.val‖ ^ 2) *
        (euclideanPartial i u (r • w.val) * euclideanPartial i v (r • w.val)))) =
      radialCutoffIntegral η * (euclideanPartial i u w.val * euclideanPartial i v w.val) := by
    rw [radialCutoffIntegral, ← integral_mul_const]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro r hr
    have hw : ‖w.val‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using w.property
    have hw0 : w.val ≠ 0 := by intro he; simp [he] at hw
    dsimp [euclideanPartial, u, v]
    rw [harmonicAngularExtension_fderiv_scale hQ hr hw0,
      harmonicAngularExtension_fderiv_scale hP hr hw0,
      norm_smul, Real.norm_eq_abs, abs_of_pos hr, hw, mul_one]
    try simp only [smul_eq_mul]
    field_simp [(show 0 < r from hr).ne']
  simp_rw [he]
  rw [integral_const_mul]

end TheoremT.HydrogenPolynomial
