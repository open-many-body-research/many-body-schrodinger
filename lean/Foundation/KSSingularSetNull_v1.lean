import NuclearKSLift_v1
import KSMapHessian_v1

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem nuclear_KS_transverse_zero_null {N : ℕ} (i : Fin N) :
    volume {q : NuclearKSSpace i | q.1=0}=0 := by
  have he : {q : NuclearKSSpace i | q.1=0} =
      ({0} : Set KSSpace) ×ˢ (Set.univ : Set (SpectatorConfiguration i)) := by
    ext q
    simp
  rw [he]
  change ((volume : Measure KSSpace).prod volume) _ = 0
  rw [Measure.prod_prod]
  simp

theorem nuclear_KS_selected_collision_null {N : ℕ} (i : Fin N) :
    volume {q : NuclearKSSpace i | position (nuclearKSLift i q) i=0}=0 := by
  have he : {q : NuclearKSSpace i | position (nuclearKSLift i q) i=0}={q | q.1=0} := by
    ext q
    simp only [Set.mem_setOf_eq,nuclearKSLift_selected_position,ksMap_eq_zero_iff]
  rw [he,nuclear_KS_transverse_zero_null]

#print axioms nuclear_KS_transverse_zero_null
#print axioms nuclear_KS_selected_collision_null
end TheoremT.Continuum
