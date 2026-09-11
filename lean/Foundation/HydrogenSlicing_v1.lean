import HydrogenCompactComplex_v1
import NuclearHardySlicing_v2

/-! Sharp nuclear Coulomb completing-square inequality on actual configuration
space. Electron slicing carries exactly three directional derivatives. -/
noncomputable section
set_option maxHeartbeats 1200000
open MeasureTheory
open scoped BigOperators ContDiff
namespace TheoremT.Continuum

theorem nuclear_coulomb_on_slice {N : ℕ} (i : Fin N) {t : ℝ} (ht : 0 < t)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    (s : SpectatorConfiguration i) :
    Integrable (fun y : Position => ‖u (configurationReassemble i y s)‖^2 / ‖y‖) volume ∧
      2*t*(∫ y : Position, ‖u (configurationReassemble i y s)‖^2 / ‖y‖) ≤
        (∫ y : Position, electronGradientEnergy i u (configurationReassemble i y s)) +
          t^2*(∫ y : Position, ‖u (configurationReassemble i y s)‖^2) := by
  have h := TheoremT.Hydrogen.compact_complex_coulomb_bound ht
    (hu.comp (contDiff_configurationReassemble_left i s)) (compactSupport_configuration_slice i huc s)
  simpa only [Function.comp_def, configuration_slice_fderiv_basis i hu, electronGradientEnergy] using h

theorem electronGradientEnergy_slice_integrable {N : ℕ} (i : Fin N)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    (s : SpectatorConfiguration i) :
    Integrable (fun y : Position => electronGradientEnergy i u (configurationReassemble i y s)) := by
  have hv := hu.comp (contDiff_configurationReassemble_left i s)
  have hc := compactSupport_configuration_slice i huc s
  have h (k : Fin 3) := (((hv.continuous_fderiv_apply (by norm_num)).comp
    (continuous_id.prodMk continuous_const)).memLp_of_hasCompactSupport
      (p := 2) (μ := volume) (hc.fderiv_apply ℝ (TheoremT.Hardy.basisVector k))).integrable_norm_pow
        (by norm_num : (2 : ℕ) ≠ 0)
  have hh := integrable_finsetSum Finset.univ (fun k _ => h k)
  change Integrable (fun y : Position => ∑ k : Fin 3,
    ‖fderiv ℝ (fun z => u (configurationReassemble i z s)) y (TheoremT.Hardy.basisVector k)‖^2) at hh
  simpa only [configuration_slice_fderiv_basis i hu, electronGradientEnergy] using hh

theorem compact_nuclear_coulomb_bound {N : ℕ} (i : Fin N) {t : ℝ} (ht : 0 < t)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x : Configuration N => ‖u x‖^2 / ‖position x i‖) volume ∧
      2*t*(∫ x : Configuration N, ‖u x‖^2 / ‖position x i‖) ≤
        (∫ x : Configuration N, electronGradientEnergy i u x) +
          t^2*(∫ x : Configuration N, ‖u x‖^2) := by
  have hg := electronGradientEnergy_integrable i hu huc
  have hm := (hu.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) huc).integrable_norm_pow
    (by norm_num : (2 : ℕ) ≠ 0)
  have h := integrable_and_bound_of_slices i
    (fun x : Configuration N => ‖u x‖^2 / ‖position x i‖)
    (fun x => electronGradientEnergy i u x + t^2 * ‖u x‖^2) (2*t)⁻¹
    ((hu.continuous.measurable.norm.pow_const 2).div ((continuous_position i).measurable.norm))
    (fun x => by positivity) (hg.add (hm.const_mul (t^2)))
    (fun s => by simpa only [configurationReassemble_position] using
      (nuclear_coulomb_on_slice i ht hu huc s).1) ?_
  · refine ⟨h.1, ?_⟩
    have he := integral_add hg (hm.const_mul (t^2))
    simp only [Pi.add_apply, Function.comp_def] at he
    rw [he, integral_const_mul, ← div_eq_inv_mul] at h
    simpa only [mul_comm] using (le_div_iff₀ (by positivity : 0 < 2*t)).1 h.2
  · intro s
    have hgs := electronGradientEnergy_slice_integrable i hu huc s
    have hms := (((hu.comp (contDiff_configurationReassemble_left i s)).continuous).memLp_of_hasCompactSupport (p := 2) (μ := volume) (compactSupport_configuration_slice i huc s)).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have he := integral_add hgs (hms.const_mul (t^2))
    simp only [Pi.add_apply, Function.comp_def] at he
    rw [he, integral_const_mul, ← div_eq_inv_mul]
    apply (le_div_iff₀ (by positivity : 0 < 2*t)).2
    simpa only [configurationReassemble_position, mul_comm] using
      (nuclear_coulomb_on_slice i ht hu huc s).2

#print axioms nuclear_coulomb_on_slice
#print axioms compact_nuclear_coulomb_bound
end TheoremT.Continuum
