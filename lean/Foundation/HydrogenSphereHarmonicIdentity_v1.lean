import HydrogenAngularPolar_v1

/-! Unit-sphere harmonic energy identities for the actual Euclidean tangential
derivatives and actual sphere area measure. The auxiliary radial cutoff must
have nonzero integral; constructing one discharges this purely scalar input. -/
noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.HydrogenPolynomial

theorem sphere_harmonic_energy_identity {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hη0 : (0 : AngularR3) ∉ tsupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hηI : radialCutoffIntegral η ≠ 0)
    {P Q : MvPolynomial (Fin 3) ℝ} {m l : ℕ}
    (hP : P.IsHomogeneous m) (hLP : polynomialLaplace P = 0)
    (hQ : Q.IsHomogeneous l) :
    sphereAngularEnergy (harmonicAngularExtension l Q) (harmonicAngularExtension m P) =
      ((m : ℝ) * (m + 1)) *
        sphereAngularInner (harmonicAngularExtension l Q) (harmonicAngularExtension m P) := by
  have h := harmonicAngularExtension_weighted_identity hη hηc hη0 l hP hLP (Q := Q)
  rw [weightedAngularEnergy_polar hη hηc hη0 hP hQ,
    weightedAngularInner_polar hη hηc hη0 hP hQ] at h
  apply mul_left_cancel₀ hηI
  calc
    _ = _ := h
    _ = _ := by ring

theorem sphere_harmonic_distinct_degree_orthogonal {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hη0 : (0 : AngularR3) ∉ tsupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hηI : radialCutoffIntegral η ≠ 0)
    {P Q : MvPolynomial (Fin 3) ℝ} {m l : ℕ}
    (hP : P.IsHomogeneous m) (hLP : polynomialLaplace P = 0)
    (hQ : Q.IsHomogeneous l) (hLQ : polynomialLaplace Q = 0) (hml : m ≠ l) :
    sphereAngularInner (harmonicAngularExtension l Q) (harmonicAngularExtension m P) = 0 := by
  have h := harmonicAngularExtension_weighted_orthogonal hη hηc hη0 hP hLP hQ hLQ hml
  rw [weightedAngularInner_polar hη hηc hη0 hP hQ] at h
  exact (mul_eq_zero.mp h).resolve_left hηI

theorem sphere_harmonic_positive_degree_mean_zero {η : ℝ → ℝ} (hη : ContDiff ℝ ∞ η)
    (hηc : HasCompactSupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hη0 : (0 : AngularR3) ∉ tsupport (fun x : AngularR3 => η (‖x‖ ^ 2)))
    (hηI : radialCutoffIntegral η ≠ 0)
    {P : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) (hLP : polynomialLaplace P = 0) (hm : 0 < m) :
    (∫ w : Metric.sphere (0 : AngularR3) 1,
      harmonicAngularExtension m P w.val ∂(volume : Measure AngularR3).toSphere) = 0 := by
  have h := sphere_harmonic_distinct_degree_orthogonal hη hηc hη0 hηI hP hLP
    (MvPolynomial.isHomogeneous_C (Fin 3) (1 : ℝ))
    (show polynomialLaplace (MvPolynomial.C (1 : ℝ) : MvPolynomial (Fin 3) ℝ) = 0 by
      simp [polynomialLaplace]) hm.ne'
  have hconst : harmonicAngularExtension 0 (MvPolynomial.C (1 : ℝ)) =
      (fun _ : AngularR3 => 1) := by
    funext x
    simp [harmonicAngularExtension, radialPolynomialProduct, radialSquaredPower, euclideanEvaluation]
  rw [hconst] at h
  simpa [sphereAngularInner] using h

end TheoremT.HydrogenPolynomial
