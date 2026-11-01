import NuclearKSTestIntegrability_v1
import GrushinWeightedIBP_v1
import KSScaledPrincipal_v1

/-! Integration by parts for the actual KS principal operator with arbitrary
real spectator coefficient. Smoothness is required only on the compact test
support, and both test pairings are proved integrable. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

theorem ks_scaled_principal_integration_by_parts {N : ℕ} (i : Fin N) (c : ℝ)
    {φ : NuclearKSSpace i → ℝ} {u : NuclearKSSpace i → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ u q) :
    Integrable (fun q => ksScaledRealPrincipal i c φ q • u q) volume ∧
    Integrable (fun q => φ q • ksScaledPrincipal i c u q) volume ∧
    (∫ q, ksScaledRealPrincipal i c φ q • u q) = ∫ q, φ q • ksScaledPrincipal i c u q := by
  letI := nuclearKS_volume_isAddHaar i
  let A (k : Fin 4) (q : NuclearKSSpace i) : ℂ :=
    fderiv ℝ (fun z => fderiv ℝ φ z (ksBasis k,0)) q (ksBasis k,0) • u q
  let A' (k : Fin 4) (q : NuclearKSSpace i) : ℂ :=
    φ q • fderiv ℝ (fun z => fderiv ℝ u z (ksBasis k,0)) q (ksBasis k,0)
  let C (k : SpectatorCoordinate i) (q : NuclearKSSpace i) : ℂ :=
    (‖q.1‖^2*fderiv ℝ (fun z => fderiv ℝ φ z (0,spectatorBasis k)) q (0,spectatorBasis k)) • u q
  let C' (k : SpectatorCoordinate i) (q : NuclearKSSpace i) : ℂ :=
    φ q • (‖q.1‖^2 • fderiv ℝ (fun z => fderiv ℝ u z (0,spectatorBasis k)) q (0,spectatorBasis k))
  have hA (k : Fin 4) : Integrable (A k) volume := local_second_test_smul_integrable hφ hc hu _
  have hA' (k : Fin 4) : Integrable (A' k) volume := local_test_second_smul_integrable hφ hc hu _
  have hC (k : SpectatorCoordinate i) : Integrable (C k) volume := nuclear_KS_weighted_second_test_integrable i hφ hc hu _
  have hC' (k : SpectatorCoordinate i) : Integrable (C' k) volume := nuclear_KS_test_weighted_second_integrable i hφ hc hu _
  have ha (k : Fin 4) : (∫ q,A k q) = ∫ q,A' k q := local_second_directional_integration_by_parts hφ hc hu _
  have hc' (k : SpectatorCoordinate i) : (∫ q,C k q) = ∫ q,C' k q := nuclear_KS_weighted_spectator_integration_by_parts i hφ hc hu _
  have hL : (fun q => ksScaledRealPrincipal i c φ q • u q) =
      fun q => (∑ k : Fin 4,A k q)+(c:ℝ) • (∑ k : SpectatorCoordinate i,C k q) := by
    funext q
    simp only [ksScaledRealPrincipal,A,C,add_smul,Finset.sum_smul,mul_smul,Finset.smul_sum]
  have hR : (fun q => φ q • ksScaledPrincipal i c u q) =
      fun q => (∑ k : Fin 4,A' k q)+(c:ℝ) • (∑ k : SpectatorCoordinate i,C' k q) := by
    funext q
    simp only [ksScaledPrincipal,A',C',smul_add,Finset.smul_sum,mul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact smul_comm (φ q) (c:ℝ) _
  rw [hL,hR]
  have hLA := integrable_finsetSum Finset.univ (fun k _ => hA k)
  have hRA := integrable_finsetSum Finset.univ (fun k _ => hA' k)
  have hLC := integrable_finsetSum Finset.univ (fun k _ => hC k)
  have hRC := integrable_finsetSum Finset.univ (fun k _ => hC' k)
  have hLCc : Integrable (fun q => (c:ℝ) • ∑ k,C k q) volume := hLC.smul (c:ℝ)
  have hRCc : Integrable (fun q => (c:ℝ) • ∑ k,C' k q) volume := hRC.smul (c:ℝ)
  refine ⟨hLA.add hLCc,hRA.add hRCc,?_⟩
  rw [integral_add hLA hLCc,integral_add hRA hRCc,integral_smul,integral_smul,
    integral_finsetSum _ (fun k _ => hA k),integral_finsetSum _ (fun k _ => hA' k),
    integral_finsetSum _ (fun k _ => hC k),integral_finsetSum _ (fun k _ => hC' k)]
  simp only [ha,hc']

#print axioms ks_scaled_principal_integration_by_parts
end TheoremT.Continuum
