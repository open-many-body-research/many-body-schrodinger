import NuclearKSLift_v1
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace TheoremT.Continuum

theorem ksSpace_ball_volume (r : ℝ) :
    volume (Metric.ball (0 : KSSpace) r)=(ENNReal.ofReal r)^4*ENNReal.ofReal (Real.pi^2/2) := by
  have hh := InnerProductSpace.volume_ball_of_dim_even (E := KSSpace) (k := 2)
    (by simp [KSSpace]) (0 : KSSpace) r
  simpa [KSSpace] using hh

theorem nuclear_KS_tube_volume {N : ℕ} (i : Fin N)
    (r : ℝ) (T : Set (SpectatorConfiguration i)) :
    volume ((Metric.ball (0 : KSSpace) r) ×ˢ T) =
      (ENNReal.ofReal r)^4*ENNReal.ofReal (Real.pi^2/2)*volume T := by
  change ((volume : Measure KSSpace).prod volume) _ = _
  rw [Measure.prod_prod,ksSpace_ball_volume]

#print axioms ksSpace_ball_volume
#print axioms nuclear_KS_tube_volume
end TheoremT.Continuum
