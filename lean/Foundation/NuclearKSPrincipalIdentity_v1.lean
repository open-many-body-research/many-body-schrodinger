import KSProductLaplacian_v1
import ConfigurationSplitLaplacian_v1
import NuclearKSLift_v1

noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def nuclearKSPrincipal {N : ℕ} (i : Fin N) (u : NuclearKSSpace i → ℂ) (q : NuclearKSSpace i) : ℂ :=
  (∑ k : Fin 4, fderiv ℝ (fun z => fderiv ℝ u z (ksBasis k,0)) q (ksBasis k,0)) +
    (4*‖q.1‖^2) • ∑ k : SpectatorCoordinate i,
      fderiv ℝ (fun z => fderiv ℝ u z (0,spectatorBasis k)) q (0,spectatorBasis k)

theorem nuclear_KS_principal_identity {N : ℕ} (i : Fin N)
    {g : Configuration N → ℂ} (q : NuclearKSSpace i)
    (hg : ContDiffAt ℝ 2 g (nuclearKSLift i q)) :
    nuclearKSPrincipal i (g ∘ nuclearKSLift i) q =
      (4*‖q.1‖^2) • smoothLaplacian g (nuclearKSLift i q) := by
  let Φ : Position × SpectatorConfiguration i → ℂ := g ∘ (configurationProductEquiv i).symm
  have hΦ : ContDiffAt ℝ 2 Φ (ksProductMap q) :=
    hg.comp (ksProductMap q) (configurationProductEquiv i).symm.contDiff.contDiffAt
  change (∑ k : Fin 4, fderiv ℝ (fun z => fderiv ℝ (Φ ∘ ksProductMap) z (ksBasis k,0)) q (ksBasis k,0)) +
    (4*‖q.1‖^2) • (∑ k : SpectatorCoordinate i,
      fderiv ℝ (fun z => fderiv ℝ (Φ ∘ ksProductMap) z (0,spectatorBasis k)) q (0,spectatorBasis k)) = _
  rw [ksProductMap_laplacian_first q hΦ]
  simp_rw [ksProductMap_second_spectator q hΦ]
  rw [← smul_add]
  congr 1
  exact configuration_split_laplacian i (ksProductMap q) hg

#print axioms nuclear_KS_principal_identity
end TheoremT.Continuum
