import HalfLineDomainPairing_v1
import HalfLineL2Dominated_v1

/-! Integration version of actual radial kinetic cancellation. Reuses the
canonical half-line L2 norm/integral lemma, so it composes with GroundDomain.
Successful v1 is preserved; its independently defined norm lemma clashes with
HalfLineL2Dominated_v1 when those modules are imported together. -/
noncomputable section
namespace TheoremT.HalfLine

theorem radial_kinetic_cancellation_v2 (u : D) :
    ‖dJ u-W u‖^2 = ‖dJ u‖^2 := by
  rw [norm_sub_sq_real]
  have h := domain_quotient_gradient_real u
  rw [real_inner_comm] at h
  nlinarith

#print axioms radial_kinetic_cancellation_v2
end TheoremT.HalfLine
