import HydrogenSphereHarmonicIdentity_v1
import HydrogenAngularCutoff_v1

/-! The genuine sphere energy identity, orthogonality and vanishing mean with
the auxiliary cutoff fully discharged by the explicit positive bump. -/
noncomputable section
open MeasureTheory
namespace TheoremT.HydrogenPolynomial

theorem actual_sphere_harmonic_energy_identity
    {P Q : MvPolynomial (Fin 3) ℝ} {m l : ℕ}
    (hP : P.IsHomogeneous m) (hLP : polynomialLaplace P = 0)
    (hQ : Q.IsHomogeneous l) :
    sphereAngularEnergy (harmonicAngularExtension l Q) (harmonicAngularExtension m P) =
      ((m : ℝ) * (m + 1)) *
        sphereAngularInner (harmonicAngularExtension l Q) (harmonicAngularExtension m P) :=
  sphere_harmonic_energy_identity angularCutoff_contDiff
    angularCutoff_norm_sq_compact angularCutoff_norm_sq_zero_not_tsupport
    angularCutoff_radial_integral_pos.ne' hP hLP hQ

theorem actual_sphere_harmonic_distinct_degree_orthogonal
    {P Q : MvPolynomial (Fin 3) ℝ} {m l : ℕ}
    (hP : P.IsHomogeneous m) (hLP : polynomialLaplace P = 0)
    (hQ : Q.IsHomogeneous l) (hLQ : polynomialLaplace Q = 0) (hml : m ≠ l) :
    sphereAngularInner (harmonicAngularExtension l Q) (harmonicAngularExtension m P) = 0 :=
  sphere_harmonic_distinct_degree_orthogonal angularCutoff_contDiff
    angularCutoff_norm_sq_compact angularCutoff_norm_sq_zero_not_tsupport
    angularCutoff_radial_integral_pos.ne' hP hLP hQ hLQ hml

theorem actual_sphere_harmonic_positive_degree_mean_zero
    {P : MvPolynomial (Fin 3) ℝ} {m : ℕ}
    (hP : P.IsHomogeneous m) (hLP : polynomialLaplace P = 0) (hm : 0 < m) :
    (∫ w : Metric.sphere (0 : AngularR3) 1,
      harmonicAngularExtension m P w.val ∂(volume : Measure AngularR3).toSphere) = 0 :=
  sphere_harmonic_positive_degree_mean_zero angularCutoff_contDiff
    angularCutoff_norm_sq_compact angularCutoff_norm_sq_zero_not_tsupport
    angularCutoff_radial_integral_pos.ne' hP hLP hm

end TheoremT.HydrogenPolynomial
