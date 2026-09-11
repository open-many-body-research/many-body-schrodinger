import RegularizedNewtonPotential_v1
import ConfigurationRpowKernel_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace TheoremT.Continuum

def newtonPotential (N : ℕ) (x : Configuration N) : ℝ :=
  (2-(3*N:ℝ))⁻¹*‖x‖^(2-(3*N:ℝ))

theorem newtonPotential_locallyIntegrable {N : ℕ} (hN : 0 < N) :
    LocallyIntegrable (newtonPotential N) volume := by
  have h := (configuration_norm_rpow_locallyIntegrable hN
    (α := (3*N:ℝ)-2) (by linarith)).smul ((2-(3*N:ℝ))⁻¹)
  convert h using 1
  funext x
  simp only [newtonPotential,Pi.smul_apply,smul_eq_mul]
  congr 2
  ring

theorem regularizedNewtonPotential_abs_bound {N : ℕ} (hN : 0 < N)
    {δ : ℝ} (hδ : 0 < δ) {x : Configuration N} (hx : x ≠ 0) :
    |regularizedNewtonPotential N δ x| ≤
      |(2-(3*N:ℝ))⁻¹| * ‖x‖^(2-(3*N:ℝ)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hn : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hb : (2-(3*N:ℝ))/2 ≤ 0 := by linarith
  have hh := Real.rpow_le_rpow_of_nonpos (sq_pos_of_pos hr)
    (show ‖x‖^2 ≤ ‖x‖^2+δ by linarith) hb
  have he : (‖x‖^2)^((2-(3*N:ℝ))/2)=‖x‖^(2-(3*N:ℝ)) := by
    rw [← Real.rpow_natCast ‖x‖ 2,← Real.rpow_mul hr.le]
    congr 1
    ring
  rw [he] at hh
  simp only [regularizedNewtonPotential,regularizedRadialPower,abs_mul,
    abs_of_nonneg (Real.rpow_nonneg (by positivity : 0 ≤ ‖x‖^2+δ) _)]
  exact mul_le_mul_of_nonneg_left hh (abs_nonneg _)

theorem regularizedNewtonPotential_tendsto {N : ℕ}
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) {x : Configuration N} (hx : x ≠ 0) :
    Tendsto (fun n => regularizedNewtonPotential N (δ n) x) atTop (𝓝 (newtonPotential N x)) := by
  have hr : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have ht : Tendsto (fun n => ‖x‖^2+δ n) atTop (𝓝 (‖x‖^2)) := by
    simpa using tendsto_const_nhds.add hδ
  have hp := ht.rpow_const (p := (2-(3*N:ℝ))/2) (Or.inl (sq_pos_of_pos hr).ne')
  have he : (‖x‖^2)^((2-(3*N:ℝ))/2)=‖x‖^(2-(3*N:ℝ)) := by
    rw [← Real.rpow_natCast ‖x‖ 2,← Real.rpow_mul hr.le]
    congr 1
    ring
  simpa only [he,regularizedNewtonPotential,regularizedRadialPower,newtonPotential] using
    hp.const_mul ((2-(3*N:ℝ))⁻¹)

#print axioms regularizedNewtonPotential_abs_bound
#print axioms regularizedNewtonPotential_tendsto
end TheoremT.Continuum
