import LocalizedSmoothCoulombCoefficient_v1

noncomputable section
open Filter
open scoped ContDiff Topology
namespace TheoremT.Continuum

theorem smooth_smul_of_smooth_on_tsupport {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {χ : E → ℝ} {u : E → F} (hχ : ContDiff ℝ ∞ χ)
    (hu : ∀ x ∈ tsupport χ, ContDiffAt ℝ ∞ u x) :
    ContDiff ℝ ∞ (fun x => χ x • u x) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  by_cases hx : x ∈ tsupport χ
  · exact hχ.contDiffAt.smul (hu x hx)
  · apply contDiffAt_const.congr_of_eventuallyEq (f := fun _ => (0:F))
    filter_upwards [notMem_tsupport_iff_eventuallyEq.mp hx] with y hy
    simp [hy]

theorem local_contDiffAt_directional_derivative {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {u : E → F} {x : E} (hu : ContDiffAt ℝ ∞ u x) (v : E) :
    ContDiffAt ℝ ∞ (fun y => fderiv ℝ u y v) x :=
  (hu.fderiv_right (by simp : (∞ : WithTop ℕ∞)+1 ≤ ∞)).clm_apply contDiffAt_const

#print axioms smooth_smul_of_smooth_on_tsupport
#print axioms local_contDiffAt_directional_derivative
end TheoremT.Continuum
