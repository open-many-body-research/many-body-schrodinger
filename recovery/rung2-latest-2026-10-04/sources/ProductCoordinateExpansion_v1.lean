import ProductCoordinateWeakHk_v1
import Mathlib.Analysis.Normed.Lp.PiLp

/-! Exact coordinate reconstruction on the physical product, with its existing
product maximum norm. Coordinate magnitudes are bounded by this same norm;
no change to a WithLp norm or an assumed basis expansion is made. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def productCoordinateComponent (x : Space κ) : Fin 4 ⊕ κ → ℝ
  | .inl i => x.1 i
  | .inr j => x.2 j

omit [DecidableEq κ] in
theorem productCoordinateComponent_abs_le (x : Space κ) (j : Fin 4 ⊕ κ) :
    |productCoordinateComponent x j| ≤ ‖x‖ := by
  cases j with
  | inl i =>
    exact (PiLp.norm_apply_le x.1 i).trans (norm_fst_le x)
  | inr j =>
    exact (PiLp.norm_apply_le x.2 j).trans (norm_snd_le x)

theorem productCoordinateComponent_reconstruct (x : Space κ) :
    (∑ j : Fin 4 ⊕ κ, productCoordinateComponent x j • productCoordinateDirection j) = x := by
  ext i <;>
    simp [Fintype.sum_sum_type, productCoordinateComponent, productCoordinateDirection,
      yDir, tDir, oscillatorBasis, Prod.fst_sum, Prod.snd_sum,
      WithLp.ofLp_sum, Finset.sum_apply, Pi.single_apply]

end TheoremT.Continuum.WeakGrushin
