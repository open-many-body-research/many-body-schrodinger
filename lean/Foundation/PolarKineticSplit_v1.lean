import RadialTangentialAlgebra_v1
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.RealDeriv

/-! Actual radial/tangential kinetic splitting for complex-valued smooth
functions on Euclidean space. This is a pointwise identity of real derivatives. -/
noncomputable section
set_option maxHeartbeats 800000
open scoped BigOperators ContDiff
namespace TheoremT.Polar
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def complexTangentialPartial (i : ι) (f : EuclideanSpace ℝ ι → ℂ)
    (w : EuclideanSpace ℝ ι) : ℂ :=
  fderiv ℝ f w (EuclideanSpace.single i 1)-w i • fderiv ℝ f w w

theorem fderiv_scaled_argument (f : EuclideanSpace ℝ ι → ℂ)
    (hf : Differentiable ℝ f) (r : ℝ) (w v : EuclideanSpace ℝ ι) :
    fderiv ℝ (fun y => f (r • y)) w v = r • fderiv ℝ f (r • w) v := by
  have hs : HasFDerivAt (fun y : EuclideanSpace ℝ ι => r • y)
      (r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) w :=
    (hasFDerivAt_id w).const_smul r
  have h := (hf (r • w)).hasFDerivAt.comp w hs
  have he : fderiv ℝ (fun y => f (r • y)) w =
      (fderiv ℝ f (r • w)).comp (r • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) :=
    h.fderiv
  rw [he]
  simp

theorem complexTangentialPartial_scaled (f : EuclideanSpace ℝ ι → ℂ)
    (hf : Differentiable ℝ f) (r : ℝ) (w : EuclideanSpace ℝ ι) (i : ι) :
    complexTangentialPartial i (fun y => f (r • y)) w =
      r • (fderiv ℝ f (r • w) (EuclideanSpace.single i 1)-
        w i • fderiv ℝ f (r • w) w) := by
  rw [complexTangentialPartial,fderiv_scaled_argument f hf,
    fderiv_scaled_argument f hf,smul_sub,smul_comm]

theorem polar_pointwise_kinetic_split (f : EuclideanSpace ℝ ι → ℂ)
    (hf : Differentiable ℝ f) (r : ℝ) (w : EuclideanSpace ℝ ι) (hw : ‖w‖ = 1) :
    r^2 * (∑ i, ‖fderiv ℝ f (r • w) (EuclideanSpace.single i 1)‖^2) =
      r^2 * ‖fderiv ℝ f (r • w) w‖^2 +
        ∑ i, ‖complexTangentialPartial i (fun y => f (r • y)) w‖^2 := by
  have h := euclidean_unit_direction_decomposition (fderiv ℝ f (r • w)) w hw
  rw [h,mul_add]
  congr 1
  simp_rw [complexTangentialPartial_scaled f hf,norm_smul,mul_pow,
    Real.norm_eq_abs,sq_abs]
  rw [Finset.mul_sum]

#print axioms fderiv_scaled_argument
#print axioms complexTangentialPartial_scaled
#print axioms polar_pointwise_kinetic_split
end TheoremT.Polar
