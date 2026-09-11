import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Actual radial profiles of punctured smooth compact functions.
No polar weak-derivative formula or half-line domain membership is assumed. -/
noncomputable section
set_option maxHeartbeats 800000
open Set Filter
open scoped Topology ContDiff
namespace TheoremT.Polar
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def radialWhole (f : E → ℂ) (w : E) (r : ℝ) : ℂ := r • f (r • w)

theorem radialWhole_contDiff (f : E → ℂ) (hf : ContDiff ℝ ∞ f) (w : E) :
    ContDiff ℝ ∞ (radialWhole f w) :=
  contDiff_id.smul (hf.comp (contDiff_id.smul contDiff_const))

theorem radialWhole_compact (f : E → ℂ) (hc : HasCompactSupport f)
    (w : E) (hw : w ≠ 0) : HasCompactSupport (radialWhole f w) := by
  have hcomp : HasCompactSupport (fun r : ℝ => f (r • w)) :=
    hc.comp_isClosedEmbedding (isClosedEmbedding_smul_left (𝕜 := ℝ) hw)
  exact hcomp.smul_left (f := fun r : ℝ => r)

theorem radialWhole_zero_notMem_tsupport (f : E → ℂ)
    (hz : (0 : E) ∉ tsupport f) (w : E) :
    (0 : ℝ) ∉ tsupport (radialWhole f w) := by
  have hsub : tsupport (radialWhole f w) ⊆
      tsupport (fun r : ℝ => f (r • w)) :=
    tsupport_smul_subset_right (fun r : ℝ => r) (fun r : ℝ => f (r • w))
  intro h
  have hm := tsupport_comp_subset_preimage f
    (show Continuous (fun r : ℝ => r • w) by fun_prop) (hsub h)
  apply hz
  simpa only [mem_preimage,zero_smul] using hm

theorem radialWhole_hasDerivAt (f : E → ℂ) (hf : ContDiff ℝ ∞ f)
    (w : E) (r : ℝ) :
    HasDerivAt (radialWhole f w)
      (f (r • w)+r • (fderiv ℝ f (r • w) w)) r := by
  have hcomp : HasDerivAt (fun t : ℝ => f (t • w))
      (fderiv ℝ f (r • w) w) r := by
    simpa only [Function.comp_def,one_smul] using
      (hf.differentiable (by simp) (r • w)).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_id' r).smul_const w)
  simpa only [radialWhole,one_smul,add_comm] using! (hasDerivAt_id' r).fun_smul hcomp

#print axioms radialWhole_contDiff
#print axioms radialWhole_compact
#print axioms radialWhole_zero_notMem_tsupport
#print axioms radialWhole_hasDerivAt
end TheoremT.Polar
