import PairCoordinatesLaplacian_v1
import KSProductLaplacian_v1
import KSScaledPrincipal_v1

/-! The actual pair chart has spectator coefficient c=1. This identity is
pointwise for a C2 physical function; the physical eigenfunction application
will be made away from the selected collision before weak removability. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

theorem pair_KS_principal_identity {g : Configuration 2 → ℂ} (q : PairKSSpace)
    (hg : ContDiffAt ℝ 2 g (pairKSLift q)) :
    ksScaledPrincipal (0 : Fin 2) 1 (g ∘ pairKSLift) q =
      (2*‖q.1‖^2) • smoothLaplacian g (pairKSLift q) := by
  let Φ : Position × SpectatorConfiguration (0 : Fin 2) → ℂ := g ∘ pairCoordinates
  have hΦ : ContDiffAt ℝ 2 Φ (ksProductMap q) :=
    hg.comp (ksProductMap q) pairCoordinates.contDiff.contDiffAt
  change (∑ k : Fin 4, fderiv ℝ (fun z => fderiv ℝ (Φ ∘ ksProductMap) z (ksBasis k,0)) q (ksBasis k,0)) +
    (1*‖q.1‖^2) • (∑ k : SpectatorCoordinate (0 : Fin 2), fderiv ℝ
      (fun z => fderiv ℝ (Φ ∘ ksProductMap) z (0,spectatorBasis k)) q (0,spectatorBasis k)) = _
  rw [ksProductMap_laplacian_first q hΦ]
  simp_rw [ksProductMap_second_spectator q hΦ]
  rw [one_mul,mul_comm (4 : ℝ),mul_smul,← smul_add]
  rw [pair_coordinates_weighted_laplacian (ksProductMap q) hg,smul_smul,mul_comm]
  rfl

#print axioms pair_KS_principal_identity
end TheoremT.Continuum
