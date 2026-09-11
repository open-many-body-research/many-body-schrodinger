import HalfLinePhysicalForm_v1

/-! The centrifugal radial comparison on the actual half-line domain. The
integer parameter ell is an angular-order parameter; this file does not
assume or establish a three-dimensional angular decomposition. -/
noncomputable section
set_option maxHeartbeats 1000000
open MeasureTheory Set Filter
open scoped Topology
namespace TheoremT.HalfLine

def centrifugalFactor (k Z : ℝ) : D →L[ℂ] E := dJ - k • W + (Z/k) • J

theorem centrifugalFactor_apply (k Z : ℝ) (u : D) :
    centrifugalFactor k Z u = dJ u - k • W u + (Z/k) • J u := rfl

theorem centrifugal_square (k Z : ℝ) (hk : k ≠ 0) (u : D) :
    ‖centrifugalFactor k Z u‖^2 = ‖dJ u‖^2 +
      k*(k-1) * ‖W u‖^2 - 2*Z*coulombMoment u + (Z^2/k^2)*‖J u‖^2 := by
  have h := HalfLineSquareAlgebra.affine_square_identity (J u) (dJ u) (W u)
    1 k (Z/k) (domain_value_gradient_real_zero u) (domain_quotient_gradient_real u)
  rw [centrifugalFactor_apply]
  simp only [one_smul, one_pow, one_mul] at h
  rw [h]
  unfold coulombMoment
  field_simp

theorem centrifugal_lower_general (k Z : ℝ) (hk : k ≠ 0) (u : D) :
    -(Z^2/(2*k^2)) * ‖J u‖^2 ≤ q Z u + (k*(k-1)/2) * ‖W u‖^2 := by
  have h := centrifugal_square k Z hk u
  unfold q
  have hn := sq_nonneg ‖centrifugalFactor k Z u‖
  have he : Z^2/(2*k^2) = (Z^2/k^2)/2 := by ring
  rw [he]
  nlinarith

theorem centrifugal_lower (ell : ℕ) (Z : ℝ) (u : D) :
    -(Z^2/(2*((ell:ℝ)+1)^2)) * ‖J u‖^2 ≤
      q Z u + ((ell:ℝ)*((ell:ℝ)+1)/2) * ‖W u‖^2 := by
  have h := centrifugal_lower_general ((ell:ℝ)+1) Z (by positivity) u
  convert h using 1 <;> ring

theorem centrifugal_one_lower (Z : ℝ) (u : D) :
    -(Z^2/8) * ‖J u‖^2 ≤ q Z u + ‖W u‖^2 := by
  have h := centrifugal_lower 1 Z u
  norm_num at h
  simpa only [neg_mul] using h

theorem centrifugal_one_lower_physical (Z : ℝ) (u : D) :
    -(Z^2/8) * ‖J u‖^2 ≤
      (1/2)*‖dJ u‖^2 - Z*∫ x, ‖J u x‖^2/x ∂μ + ‖W u‖^2 := by
  rw [← q_physical]
  exact centrifugal_one_lower Z u

#print axioms centrifugalFactor
#print axioms centrifugalFactor_apply
#print axioms centrifugal_square
#print axioms centrifugal_lower_general
#print axioms centrifugal_lower
#print axioms centrifugal_one_lower
#print axioms centrifugal_one_lower_physical
end TheoremT.HalfLine
