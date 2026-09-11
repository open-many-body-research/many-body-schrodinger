import NewtonPotentialLimits_v1
import NewtonKernelScaling_v1
import SmoothLaplacianTransfer_v1

/-! Actual distributional Newton fundamental solution on R^(3N), N positive.
Normalization is by the proved positive integral mass, with no point-source
axiom and no deletion of the origin from the weak identity. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem newtonPotential_weak_laplacian_mass {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, realTestLaplacian φ x*newtonPotential N x)=newtonMass N*φ 0 := by
  have hε2 : Tendsto (fun n => (radiusRegularization n)^2) atTop (𝓝 (0:ℝ)) := by
    simpa using radiusRegularization_tendsto.pow 2
  have hb : LocallyIntegrable (fun x : Configuration N =>
      |(2-(3*N:ℝ))⁻¹| * ‖x‖^(2-(3*N:ℝ))) volume := by
    have hh := (configuration_norm_rpow_locallyIntegrable hN
      (α := (3*N:ℝ)-2) (by linarith)).smul |(2-(3*N:ℝ))⁻¹|
    convert hh using 1
    funext x
    simp only [Pi.smul_apply,smul_eq_mul]
    congr 2
    ring
  have hlim := compact_real_test_integral_tendsto_locally_dominated hb
    (fun n => (regularizedNewtonPotential_contDiff N
      (sq_pos_of_pos (radiusRegularization_pos n))).continuous.aestronglyMeasurable)
    (fun n => by
      filter_upwards [configuration_ae_ne_zero hN] with x hx
      rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (by positivity :
        0 ≤ |(2-(3*N:ℝ))⁻¹| * ‖x‖^(2-(3*N:ℝ)))]
      exact regularizedNewtonPotential_abs_bound hN (sq_pos_of_pos (radiusRegularization_pos n)) hx)
    (by
      filter_upwards [configuration_ae_ne_zero hN] with x hx
      exact regularizedNewtonPotential_tendsto hε2 hx)
    (realTestLaplacian_continuous hφ) (realTestLaplacian_compact hc)
  have hm := regularizedNewton_laplacian_test_tendsto hN radiusRegularization_pos
    radiusRegularization_tendsto hφ.continuous hc
  have hid (n : ℕ) :
      (∫ x, realTestLaplacian (regularizedNewtonPotential N ((radiusRegularization n)^2)) x*φ x) =
      ∫ x, realTestLaplacian φ x*regularizedNewtonPotential N ((radiusRegularization n)^2) x := by
    simpa only [mul_comm] using configuration_integral_laplacian_transfer hφ
      (regularizedNewtonPotential_contDiff N (sq_pos_of_pos (radiusRegularization_pos n))) hc
  exact tendsto_nhds_unique hlim (hm.congr' (Eventually.of_forall hid))

def normalizedNewtonPotential (N : ℕ) (x : Configuration N) : ℝ :=
  (newtonMass N)⁻¹*newtonPotential N x

theorem normalizedNewtonPotential_locallyIntegrable {N : ℕ} (hN : 0 < N) :
    LocallyIntegrable (normalizedNewtonPotential N) volume :=
  (newtonPotential_locallyIntegrable hN).smul ((newtonMass N)⁻¹)

theorem normalizedNewtonPotential_fundamental_solution {N : ℕ} (hN : 0 < N)
    {φ : Configuration N → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ x, realTestLaplacian φ x*normalizedNewtonPotential N x)=φ 0 := by
  have he : (fun x => realTestLaplacian φ x*normalizedNewtonPotential N x) =
      (fun x => (newtonMass N)⁻¹*(realTestLaplacian φ x*newtonPotential N x)) := by
    funext x; unfold normalizedNewtonPotential; ring
  rw [he,integral_const_mul,newtonPotential_weak_laplacian_mass hN hφ hc,
    ← mul_assoc,inv_mul_cancel₀ (newtonMass_pos hN).ne',one_mul]

#print axioms normalizedNewtonPotential_fundamental_solution
end TheoremT.Continuum
