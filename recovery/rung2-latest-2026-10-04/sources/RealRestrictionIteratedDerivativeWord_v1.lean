import RealCoordinateEmbedding_v1
import IteratedFDerivScalarLinearCompositionAt_v1
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Actual real-coordinate restrictions of complex functions have the
same coordinate-word derivatives as the complex derivatives on complex
coordinate unit vectors. Only local complex ContDiffAt of the requested
finite order is assumed. The conclusion follows from proved restriction
of scalars and the chain rule for the literal coordinate embedding. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
variable {ι : Type*} [Fintype ι]

theorem real_restriction_contDiffAt
    (f : (ι → ℂ) → ℂ) (z : ι → ℝ) (n : ℕ)
    (hf : ContDiffAt ℂ n f (fun i => (z i : ℂ))) :
    ContDiffAt ℝ n (fun x : ι → ℝ => f (fun i => (x i : ℂ))) z := by
  have hg : ContDiffAt ℝ n (realCoordinateEmbedding (ι := ι)) z :=
    (realCoordinateEmbedding (ι := ι)).contDiff.contDiffAt
  rw [realCoordinateEmbedding_coe] at hg
  exact (hf.restrict_scalars ℝ).comp z hg

theorem real_restriction_iteratedFDeriv_word [DecidableEq ι]
    (f : (ι → ℂ) → ℂ) (z : ι → ℝ) (n : ℕ) (w : Fin n → ι)
    (hf : ContDiffAt ℂ n f (fun i => (z i : ℂ))) :
    iteratedFDeriv ℝ n (fun x : ι → ℝ => f (fun i => (x i : ℂ))) z
        (fun j => Pi.single (w j) (1 : ℝ)) =
      iteratedFDeriv ℂ n f (fun i => (z i : ℂ))
        (fun j => Pi.single (w j) (1 : ℂ)) := by
  change iteratedFDeriv ℝ n (f ∘ realCoordinateEmbedding) z
    (fun j => Pi.single (w j) (1 : ℝ)) = _
  rw [iteratedFDeriv_comp_right_of_contDiffAt_scalar _ _ _ _ (hf.restrict_scalars ℝ),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  have hrestrict :
      (iteratedFDeriv ℂ n f (fun i => (z i : ℂ))).restrictScalars ℝ =
        iteratedFDeriv ℝ n f (fun i => (z i : ℂ)) :=
    hf.restrictScalars_iteratedFDeriv
  have hz : realCoordinateEmbedding z = (fun i => (z i : ℂ)) :=
    congrFun realCoordinateEmbedding_coe z
  rw [hz, ← hrestrict]
  simp only [ContinuousMultilinearMap.coe_restrictScalars, realCoordinateEmbedding_single]

end TheoremT.Continuum
