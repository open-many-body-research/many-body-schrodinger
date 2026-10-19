import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd

/-! The literal coordinatewise inclusion of a finite real coordinate
space into its complexification. Actual real coordinate unit vectors
map to the corresponding actual complex coordinate unit vectors. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι]

def realCoordinateEmbedding : (ι → ℝ) →L[ℝ] (ι → ℂ) :=
  ContinuousLinearMap.pi (fun i => Complex.ofRealCLM.comp
    (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ))

theorem realCoordinateEmbedding_coe :
    (realCoordinateEmbedding : (ι → ℝ) → (ι → ℂ)) = (fun x i => (x i : ℂ)) := rfl

theorem realCoordinateEmbedding_single [DecidableEq ι] (i : ι) :
    realCoordinateEmbedding (Pi.single i (1 : ℝ)) = Pi.single i (1 : ℂ) := by
  ext j
  by_cases h : j = i
  · subst j
    simp [realCoordinateEmbedding]
  · simp [realCoordinateEmbedding, h]

end TheoremT.Continuum
