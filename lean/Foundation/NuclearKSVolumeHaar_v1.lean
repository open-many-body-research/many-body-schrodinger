import NuclearKSLift_v1
import Mathlib.MeasureTheory.Group.Measure

noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem nuclearKS_volume_isAddHaar {N : ℕ} (i : Fin N) :
    (volume : Measure (NuclearKSSpace i)).IsAddHaarMeasure := by
  exact
    { toIsFiniteMeasureOnCompacts := inferInstance
      toIsAddLeftInvariant := by
        change ((volume : Measure KSSpace).prod (volume : Measure (SpectatorConfiguration i))).IsAddLeftInvariant
        infer_instance
      toIsOpenPosMeasure := inferInstance }

#print axioms nuclearKS_volume_isAddHaar
end TheoremT.Continuum
