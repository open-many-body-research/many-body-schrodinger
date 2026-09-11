import HydrogenAngularGreenSum_v1

/-! Actual weighted Euclidean angular energy identities. The cutoff is an
arbitrary smooth function of squared radius, compactly supported off the origin.
These identities are proved before any angular spectral or Poincaré theorem. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenPolynomial

abbrev AngularR3 := EuclideanSpace ℝ (Fin 3)

def weightedAngularInner (η : ℝ → ℝ) (u v : AngularR3 → ℝ) : ℝ :=
  ∫ x, η (‖x‖ ^ 2) / ‖x‖ ^ 2 * u x * v x

def weightedAngularEnergy (η : ℝ → ℝ) (u v : AngularR3 → ℝ) : ℝ :=
  ∑ i : Fin 3, ∫ x, η (‖x‖ ^ 2) * (euclideanPartial i u x * euclideanPartial i v x)

theorem weightedAngularInner_comm (η : ℝ → ℝ) (u v : AngularR3 → ℝ) :
    weightedAngularInner η u v = weightedAngularInner η v u := by
  unfold weightedAngularInner
  congr 1
  funext x
  ring

theorem weightedAngularEnergy_comm (η : ℝ → ℝ) (u v : AngularR3 → ℝ) :
    weightedAngularEnergy η u v = weightedAngularEnergy η v u := by
  unfold weightedAngularEnergy
  congr 1
  funext i
  congr 1
  funext x
  ring

theorem harmonicAngularExtension_weighted_identity {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hη0 : (0 : AngularR3) ∉ tsupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    {P Q : MvPolynomial (Fin 3) ℝ} {m : ℕ} (l : ℕ)
    (hP : P.IsHomogeneous m) (hL : polynomialLaplace P = 0) :
    weightedAngularEnergy η (harmonicAngularExtension l Q) (harmonicAngularExtension m P) =
      ((m : ℝ) * (m + 1)) *
        weightedAngularInner η (harmonicAngularExtension l Q) (harmonicAngularExtension m P) := by
  let χ : AngularR3 → ℝ := fun x => η (‖x‖ ^ 2)
  let u := harmonicAngularExtension l Q
  let v := harmonicAngularExtension m P
  have hχ : ContDiff ℝ ∞ χ := hη.comp (contDiff_norm_sq ℝ)
  have hu := fun x (hx : x ≠ 0) => harmonicAngularExtension_contDiffAt l Q hx
  have hv := fun x (hx : x ≠ 0) => harmonicAngularExtension_contDiffAt m P hx
  have hg := punctured_cutoff_green_sum hχ hηc hη0 hu hv
  have hc : (fun x : AngularR3 => u x * ∑ i : Fin 3,
      euclideanPartial i χ x * euclideanPartial i v x) = fun _ => 0 := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [χ, squaredRadiusCutoff_partial hη]
    · rw [show (∑ i : Fin 3, euclideanPartial i χ x * euclideanPartial i v x) = 0 from
        squaredRadiusCutoff_angular_cross_zero hη hP hx]
      simp
  rw [hc, integral_zero, sub_zero] at hg
  have he : (∫ x : AngularR3, χ x * u x * ∑ i : Fin 3,
      euclideanPartial i (euclideanPartial i v) x) =
        -((m : ℝ) * (m + 1)) * weightedAngularInner η u v := by
    rw [weightedAngularInner, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [(volume : Measure AngularR3).ae_ne 0] with x hx
    have hLap := harmonicAngularExtension_laplace hP hL hx
    change (∑ i : Fin 3, euclideanPartial i (euclideanPartial i v) x) = _ at hLap
    rw [hLap]
    dsimp [χ, v]
    ring
  rw [he] at hg
  change -((m : ℝ) * (m + 1)) * weightedAngularInner η u v =
    -weightedAngularEnergy η u v at hg
  dsimp [u, v] at hg
  linarith

theorem harmonicAngularExtension_weighted_orthogonal {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hη0 : (0 : AngularR3) ∉ tsupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    {P Q : MvPolynomial (Fin 3) ℝ} {m l : ℕ}
    (hP : P.IsHomogeneous m) (hLP : polynomialLaplace P = 0)
    (hQ : Q.IsHomogeneous l) (hLQ : polynomialLaplace Q = 0) (hml : m ≠ l) :
    weightedAngularInner η (harmonicAngularExtension l Q) (harmonicAngularExtension m P) = 0 := by
  have hm := harmonicAngularExtension_weighted_identity hη hηc hη0 l hP hLP (Q := Q)
  have hl := harmonicAngularExtension_weighted_identity hη hηc hη0 m hQ hLQ (Q := P)
  rw [weightedAngularEnergy_comm η (harmonicAngularExtension m P),
    weightedAngularInner_comm η (harmonicAngularExtension m P)] at hl
  have hne : (m : ℝ) * (m + 1) ≠ (l : ℝ) * (l + 1) := by
    intro heq
    have hnm : (0 : ℝ) ≤ m := Nat.cast_nonneg _
    have hnl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
    have hdiff : (m : ℝ) = l := by nlinarith [sq_nonneg ((m : ℝ) - l)]
    exact hml (Nat.cast_injective hdiff)
  apply (mul_eq_zero.mp (show
    ((m : ℝ) * (m + 1) - (l : ℝ) * (l + 1)) *
      weightedAngularInner η (harmonicAngularExtension l Q) (harmonicAngularExtension m P) = 0 by
        nlinarith [hm, hl])).resolve_left (sub_ne_zero.mpr hne)

end TheoremT.HydrogenPolynomial
