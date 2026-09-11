import RegularizedNewtonPotential_v1
import NewtonKernelMass_v1
import IntegrableRescalingLimit_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

theorem radial_mass_scaling_factor {ε : ℝ} (hε : 0 < ε) (d : ℕ) :
    ε^d*ε^2*(ε^2)^(-((d:ℝ)+2)/2)=1 := by
  rw [← Real.rpow_natCast ε d,← Real.rpow_natCast ε 2,← Real.rpow_mul hε.le,
    ← Real.rpow_add hε,← Real.rpow_add hε]
  norm_num only [Nat.cast_ofNat]
  rw [show (d:ℝ)+2+2*(-((d:ℝ)+2)/2)=0 by ring,Real.rpow_zero]

theorem regularizedNewton_laplacian_scaled {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (y : Configuration N) :
    ε^(3*N)*realTestLaplacian (regularizedNewtonPotential N (ε^2)) (ε • y)=newtonMassKernel N y := by
  rw [regularizedNewtonPotential_laplacian hN (sq_pos_of_pos hε)]
  have hs : ‖ε • y‖^2+ε^2=ε^2*(1+‖y‖^2) := by
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos hε,mul_pow]
    ring
  rw [hs,Real.mul_rpow (sq_nonneg ε) (by positivity : 0 ≤ 1+‖y‖^2)]
  have hf := radial_mass_scaling_factor hε (3*N)
  simp only [Nat.cast_mul,Nat.cast_ofNat] at hf
  unfold newtonMassKernel
  calc
    _ = (3*N:ℝ)*(ε^(3*N)*ε^2*(ε^2)^(-((3*N:ℝ)+2)/2))*
      (1+‖y‖^2)^(-((3*N:ℝ)+2)/2) := by ring
    _ = _ := by rw [hf,mul_one]

theorem regularizedNewton_laplacian_test_rescale {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (φ : Configuration N → ℝ) :
    (∫ x, realTestLaplacian (regularizedNewtonPotential N (ε^2)) x*φ x) =
      ∫ y, newtonMassKernel N y*φ (ε • y) := by
  have he := Measure.integral_comp_smul volume
    (fun x => realTestLaplacian (regularizedNewtonPotential N (ε^2)) x*φ x) ε
  rw [configuration_finrank,abs_of_pos (inv_pos.mpr (pow_pos hε _)),smul_eq_mul] at he
  calc
    _ = ε^(3*N)*(∫ y, realTestLaplacian (regularizedNewtonPotential N (ε^2)) (ε • y)*φ (ε • y)) := by
      rw [he]
      field_simp
    _ = ∫ y, ε^(3*N)*(realTestLaplacian (regularizedNewtonPotential N (ε^2)) (ε • y)*φ (ε • y)) :=
      (integral_const_mul _ _).symm
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rw [← mul_assoc,regularizedNewton_laplacian_scaled hN hε]

theorem regularizedNewton_laplacian_test_tendsto {N : ℕ} (hN : 0 < N)
    {ε : ℕ → ℝ} (hεp : ∀ n, 0 < ε n) (hε : Tendsto ε atTop (𝓝 0))
    {φ : Configuration N → ℝ} (hφ : Continuous φ) (hc : HasCompactSupport φ) :
    Tendsto (fun n => ∫ x, realTestLaplacian (regularizedNewtonPotential N ((ε n)^2)) x*φ x)
      atTop (𝓝 (newtonMass N*φ 0)) := by
  simp_rw [regularizedNewton_laplacian_test_rescale hN (hεp _)]
  exact integrable_kernel_dilation_test_tendsto (newtonMassKernel_integrable N) hε hφ hc

#print axioms regularizedNewton_laplacian_test_tendsto
end TheoremT.Continuum
