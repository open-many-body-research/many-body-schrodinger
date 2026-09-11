import HardyLimitComposition_v1
import Mathlib.Analysis.Complex.RealDeriv

/-! Complex-valued C¹ compact Hardy on actual Euclidean R³.
The proof splits real and imaginary components and makes no weak Sobolev density claim. -/
noncomputable section
set_option maxHeartbeats 500000
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Hardy

private theorem complex_norm_sq_split (z : ℂ) :
    ‖z‖^2 = z.re^2 + z.im^2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem fderiv_complex_re {u : R3 → ℂ}
    (hu : ContDiff ℝ 1 u) (x v : R3) :
    fderiv ℝ (fun y => (u y).re) x v = (fderiv ℝ u x v).re := by
  have h := Complex.reCLM.hasFDerivAt.comp x
    ((hu.differentiable (by norm_num) x).hasFDerivAt)
  exact congrArg (fun L : R3 →L[ℝ] ℝ => L v) h.fderiv

private theorem fderiv_complex_im {u : R3 → ℂ}
    (hu : ContDiff ℝ 1 u) (x v : R3) :
    fderiv ℝ (fun y => (u y).im) x v = (fderiv ℝ u x v).im := by
  have h := Complex.imCLM.hasFDerivAt.comp x
    ((hu.differentiable (by norm_num) x).hasFDerivAt)
  exact congrArg (fun L : R3 →L[ℝ] ℝ => L v) h.fderiv

private theorem real_derivative_energy_integrable {u : R3 → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x => ∑ i : Fin 3, (fderiv ℝ u x (basisVector i))^2) := by
  apply integrable_finsetSum
  intro i _
  have hd : Continuous (fun x => fderiv ℝ u x (basisVector i)) :=
    (hu.continuous_fderiv_apply (by norm_num)).comp
      (continuous_id.prodMk continuous_const)
  apply (hd.pow 2).integrable_of_hasCompactSupport
  apply (huc.fderiv_apply ℝ (basisVector i)).mono
  intro x hx
  simp only [Function.mem_support] at hx ⊢
  intro hz
  apply hx
  change (fderiv ℝ u x (basisVector i))^2 = 0
  rw [hz]
  norm_num

/-- Complex-valued Hardy: the weighted square is integrable and bounded by four
times the sum of the three squared directional-derivative norms. -/
theorem complex_hardy_integrable_sq_and_bound {u : R3 → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x => ‖u x‖^2 / ‖x‖^2) volume ∧
      (∫ x, ‖u x‖^2 / ‖x‖^2) ≤
        4 * (∫ x, ∑ i : Fin 3, ‖fderiv ℝ u x (basisVector i)‖^2) := by
  have hre : ContDiff ℝ 1 (fun x => (u x).re) := Complex.reCLM.contDiff.comp hu
  have him : ContDiff ℝ 1 (fun x => (u x).im) := Complex.imCLM.contDiff.comp hu
  have hcre : HasCompactSupport (fun x => (u x).re) := huc.comp_left (by rfl)
  have hcim : HasCompactSupport (fun x => (u x).im) := huc.comp_left (by rfl)
  have hr := hardy_integrable_sq_and_bound hre hcre
  have hi := hardy_integrable_sq_and_bound him hcim
  have hgr := real_derivative_energy_integrable hre hcre
  have hgi := real_derivative_energy_integrable him hcim
  have hw : (fun x : R3 => ‖u x‖^2 / ‖x‖^2) =
      (fun x => (u x).re^2 / ‖x‖^2 + (u x).im^2 / ‖x‖^2) := by
    funext x
    rw [complex_norm_sq_split, add_div]
  have hg : (fun x : R3 => ∑ i : Fin 3, ‖fderiv ℝ u x (basisVector i)‖^2) =
      (fun x => (∑ i : Fin 3, (fderiv ℝ (fun y => (u y).re) x (basisVector i))^2) +
        ∑ i : Fin 3, (fderiv ℝ (fun y => (u y).im) x (basisVector i))^2) := by
    funext x
    simp_rw [complex_norm_sq_split, fderiv_complex_re hu, fderiv_complex_im hu,
      Finset.sum_add_distrib]
  constructor
  · rw [hw]
    exact hr.1.add hi.1
  · calc
      (∫ x, ‖u x‖^2 / ‖x‖^2) =
          (∫ x, (u x).re^2 / ‖x‖^2) + (∫ x, (u x).im^2 / ‖x‖^2) := by
        rw [hw, integral_add hr.1 hi.1]
      _ ≤ 4 * (∫ x, ∑ i : Fin 3, (fderiv ℝ (fun y => (u y).re) x (basisVector i))^2) +
          4 * (∫ x, ∑ i : Fin 3, (fderiv ℝ (fun y => (u y).im) x (basisVector i))^2) :=
        add_le_add hr.2 hi.2
      _ = 4 * (∫ x, ∑ i : Fin 3, ‖fderiv ℝ u x (basisVector i)‖^2) := by
        rw [hg, integral_add hgr hgi]
        exact (mul_add 4 _ _).symm

set_option pp.proofs false in
#print complex_hardy_integrable_sq_and_bound
#print axioms complex_hardy_integrable_sq_and_bound
end TheoremT.Hardy
