import NuclearHardySlicing_v2
import ShiftedHardy3_v2

/-! Compact-C1 electron-pair Hardy bounds from translated physical slices.
The other electron remains a fixed spectator on the slice. This avoids imposing
weak slice regularity and needs no pair-coordinate rotation. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace TheoremT.Continuum

theorem configurationReassemble_other_position {N : ℕ} (i j : Fin N)
    (hij : i ≠ j) (y : Position) (s : SpectatorConfiguration i) :
    position (configurationReassemble i y s) j =
      position (configurationReassemble i 0 s) j := by
  apply (WithLp.ext_iff 2).mpr
  funext k
  exact (configurationReassemble_spectator i y s ⟨(j, k), Ne.symm hij⟩).trans
    (configurationReassemble_spectator i 0 s ⟨(j, k), Ne.symm hij⟩).symm

theorem pair_hardy_on_slice {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u)
    (s : SpectatorConfiguration i) :
    Integrable (fun y : Position => ‖u (configurationReassemble i y s)‖^2 /
      ‖position (configurationReassemble i y s) i - position (configurationReassemble i y s) j‖^2)
      volume ∧
      (∫ y : Position, ‖u (configurationReassemble i y s)‖^2 /
        ‖position (configurationReassemble i y s) i - position (configurationReassemble i y s) j‖^2) ≤
        4 * (∫ y : Position, electronGradientEnergy i u (configurationReassemble i y s)) := by
  have h := TheoremT.Hardy.shifted_complex_hardy_integrable_sq_and_bound
    (hu.comp (contDiff_configurationReassemble_left i s)) (compactSupport_configuration_slice i huc s)
    (position (configurationReassemble i 0 s) j)
  simpa only [Function.comp_def, configurationReassemble_position,
    configurationReassemble_other_position i j hij,
    configuration_slice_fderiv_basis i hu, electronGradientEnergy] using h

/-- Each pair term is controlled by the three derivatives of either selected
electron. This theorem selects the first electron i. -/
theorem compact_pair_hardy_integrable_sq_and_bound {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x : Configuration N => ‖u x‖^2 / ‖position x i - position x j‖^2) volume ∧
      (∫ x : Configuration N, ‖u x‖^2 / ‖position x i - position x j‖^2) ≤
        4 * (∫ x : Configuration N, electronGradientEnergy i u x) := by
  apply integrable_and_bound_of_slices i _ (electronGradientEnergy i u) 4
  · exact (hu.continuous.measurable.norm.pow_const 2).div
      (((continuous_position i).sub (continuous_position j)).measurable.norm.pow_const 2)
  · intro x
    positivity
  · exact electronGradientEnergy_integrable i hu huc
  · intro s
    exact (pair_hardy_on_slice i j hij hu huc s).1
  · intro s
    exact (pair_hardy_on_slice i j hij hu huc s).2

/-- A symmetric squared-integral bound obtained from the two valid one-electron
bounds. No claim of optimality is made. -/
theorem compact_pair_hardy_symmetric_sq_bound {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (∫ x : Configuration N, ‖u x‖^2 / ‖position x i - position x j‖^2) ≤
      2 * ((∫ x : Configuration N, electronGradientEnergy i u x) +
        (∫ x : Configuration N, electronGradientEnergy j u x)) := by
  have hi := (compact_pair_hardy_integrable_sq_and_bound i j hij hu huc).2
  have hj := (compact_pair_hardy_integrable_sq_and_bound j i hij.symm hu huc).2
  have heq : (fun x : Configuration N => ‖u x‖^2 / ‖position x j - position x i‖^2) =
      (fun x : Configuration N => ‖u x‖^2 / ‖position x i - position x j‖^2) := by
    funext x
    rw [norm_sub_rev]
  rw [heq] at hj
  linarith

#print axioms configurationReassemble_other_position
#print axioms pair_hardy_on_slice
#print axioms compact_pair_hardy_integrable_sq_and_bound
#print axioms compact_pair_hardy_symmetric_sq_bound

end TheoremT.Continuum
