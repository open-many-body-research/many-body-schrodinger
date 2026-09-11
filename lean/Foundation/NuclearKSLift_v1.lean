import KSMapGeometry_v1
import ConfigurationSlicing_v2
import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! A concrete KS lift of a specified electron position, retaining every
spectator coordinate. No other collision denominator is cleared by this map. -/
noncomputable section
open scoped ContDiff
namespace TheoremT.Continuum

abbrev NuclearKSSpace {N : ℕ} (i : Fin N) := KSSpace × SpectatorConfiguration i

def nuclearKSLift {N : ℕ} (i : Fin N) (q : NuclearKSSpace i) : Configuration N :=
  (configurationProductEquiv i).symm (ksMap q.1,q.2)

theorem nuclearKSLift_contDiff {N : ℕ} (i : Fin N) : ContDiff ℝ ∞ (nuclearKSLift i) :=
  (configurationProductEquiv i).symm.contDiff.comp ((ksMap_contDiff.comp contDiff_fst).prodMk contDiff_snd)

theorem nuclearKSLift_locallyLipschitz {N : ℕ} (i : Fin N) : LocallyLipschitz (nuclearKSLift i) :=
  ((nuclearKSLift_contDiff i).of_le (by simp : (1:WithTop ℕ∞) ≤ ∞)).locallyLipschitz

theorem nuclearKSLift_selected_position {N : ℕ} (i : Fin N) (q : NuclearKSSpace i) :
    position (nuclearKSLift i q) i=ksMap q.1 := by
  have h := congrArg Prod.fst ((configurationProductEquiv i).apply_symm_apply (ksMap q.1,q.2))
  exact h

theorem nuclearKSLift_nuclear_radius {N : ℕ} (i : Fin N) (q : NuclearKSSpace i) :
    ‖position (nuclearKSLift i q) i‖=‖q.1‖^2 := by
  rw [nuclearKSLift_selected_position,ksMap_norm]

#print axioms nuclearKSLift_contDiff
#print axioms nuclearKSLift_selected_position
#print axioms nuclearKSLift_nuclear_radius
end TheoremT.Continuum
