import GrushinHoleCommutator_v1
import Mathlib.Analysis.InnerProductSpace.Calculus

noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum
variable {S : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]

theorem ks_spectator_weight_contDiff :
    ContDiff ℝ ∞ (fun q : KSSpace × S => ‖q.1‖^2) := (contDiff_norm_sq ℝ).comp contDiff_fst

theorem ks_spectator_weight_second_product {φ : KSSpace × S → ℝ}
    (hφ : ContDiff ℝ ∞ φ) (q : KSSpace × S) (v : S) :
    fderiv ℝ (fun z => fderiv ℝ (fun w : KSSpace × S => ‖w.1‖^2*φ w) z (0,v)) q (0,v) =
      ‖q.1‖^2*fderiv ℝ (fun z => fderiv ℝ φ z (0,v)) q (0,v) := by
  have hA : ContDiff ℝ ∞ (fun y : KSSpace => ‖y‖^2) := contDiff_norm_sq ℝ
  rw [second_directional_product ks_spectator_weight_contDiff hφ]
  rw [first_directional_fst (hA.differentiable (by simp)),second_directional_fst hA]
  simp

#print axioms ks_spectator_weight_second_product
end TheoremT.Continuum
