import KSTubeVolume_v1
import CoulombLipschitzPointBound_v1

noncomputable section
open MeasureTheory
open scoped ENNReal
namespace TheoremT.Continuum

theorem nuclear_KS_tube_squared_mass_le {N : ℕ} (i : Fin N)
    {g : NuclearKSSpace i → ℂ} {M : ℝ} (hM : ∀ q, ‖g q‖ ≤ M)
    (r : ℝ) (T : Set (SpectatorConfiguration i)) :
    (∫⁻ q in (Metric.ball (0 : KSSpace) r) ×ˢ T, ‖g q‖ₑ^2) ≤
      (ENNReal.ofReal M)^2*((ENNReal.ofReal r)^4*ENNReal.ofReal (Real.pi^2/2)*volume T) := by
  have hb (q : NuclearKSSpace i) : ‖g q‖ₑ ≤ ENNReal.ofReal M := by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hM q)
  have hh := lintegral_mono (μ := volume.restrict ((Metric.ball (0 : KSSpace) r) ×ˢ T))
    (fun q => pow_le_pow_left' (hb q) 2)
  simpa only [lintegral_const,Measure.restrict_apply_univ,nuclear_KS_tube_volume] using hh

theorem scalar_coulomb_nuclear_KS_tube_squared_mass {N : ℕ} (hN : 0 < N)
    {Z E : ℝ} {f : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f ((E : ℂ) • f))
    {u : Configuration N → ℂ} (hu : Continuous u)
    (hEq : (f : Configuration N → ℂ) =ᵐ[volume] u)
    (i : Fin N) (r : ℝ) (T : Set (SpectatorConfiguration i)) :
    (∫⁻ q in (Metric.ball (0 : KSSpace) r) ×ˢ T, ‖u (nuclearKSLift i q)‖ₑ^2) ≤
      (ENNReal.ofReal (coulombMoserBoundCoefficient N Z E*‖f‖))^2*
        ((ENNReal.ofReal r)^4*ENNReal.ofReal (Real.pi^2/2)*volume T) :=
  nuclear_KS_tube_squared_mass_le i
    (fun q => scalar_coulomb_continuous_representative_bound hN hg hu hEq _) r T

#print axioms nuclear_KS_tube_squared_mass_le
#print axioms scalar_coulomb_nuclear_KS_tube_squared_mass
end TheoremT.Continuum
