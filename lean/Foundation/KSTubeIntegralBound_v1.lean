import KSTubeVolume_v1
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace TheoremT.Continuum

theorem nuclear_KS_tube_volume_real {N : ℕ} (i : Fin N) {r : ℝ} (hr : 0 ≤ r)
    (T : Set (SpectatorConfiguration i)) :
    volume.real ((Metric.ball (0 : KSSpace) r) ×ˢ T) = r^4*(Real.pi^2/2)*volume.real T := by
  simp only [measureReal_def,nuclear_KS_tube_volume,ENNReal.toReal_mul,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr,ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi^2/2)]

theorem nuclear_KS_supported_integral_bound {N : ℕ} (i : Fin N)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    {g : NuclearKSSpace i → G} {A δ : ℝ} (hδ : 0 < δ)
    (T : Set (SpectatorConfiguration i)) (hT : volume T ≠ ⊤)
    (hs : ∀ q, q ∉ (Metric.ball (0 : KSSpace) (3*δ)) ×ˢ T → g q=0)
    (hb : ∀ q, ‖g q‖ ≤ A/δ^2) :
    ‖∫ q, g q‖ ≤ 81*A*(Real.pi^2/2)*volume.real T*δ^2 := by
  have hfin : volume ((Metric.ball (0 : KSSpace) (3*δ)) ×ˢ T) < ⊤ := by
    rw [nuclear_KS_tube_volume]
    exact ENNReal.mul_lt_top (by finiteness) hT.lt_top
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hs]
  apply (norm_setIntegral_le_of_norm_le_const hfin (fun q _ => hb q)).trans_eq
  rw [nuclear_KS_tube_volume_real i (by positivity)]
  field_simp
  <;> ring

#print axioms nuclear_KS_supported_integral_bound
end TheoremT.Continuum
