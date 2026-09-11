import NuclearKSTestIntegrability_v1
import GrushinWeightedIBP_v1
import NuclearKSPrincipalIdentity_v1

noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum

def nuclearKSRealPrincipal {N : ℕ} (i : Fin N) (φ : NuclearKSSpace i → ℝ) (q : NuclearKSSpace i) : ℝ :=
  (∑ k : Fin 4, fderiv ℝ (fun z => fderiv ℝ φ z (ksBasis k,0)) q (ksBasis k,0)) +
    4*‖q.1‖^2*(∑ k : SpectatorCoordinate i,
      fderiv ℝ (fun z => fderiv ℝ φ z (0,spectatorBasis k)) q (0,spectatorBasis k))

theorem nuclear_KS_principal_integration_by_parts {N : ℕ} (i : Fin N)
    {φ : NuclearKSSpace i → ℝ} {u : NuclearKSSpace i → ℂ}
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    (hu : ∀ q ∈ tsupport φ, ContDiffAt ℝ ∞ u q) :
    Integrable (fun q => nuclearKSRealPrincipal i φ q • u q) volume ∧
    Integrable (fun q => φ q • nuclearKSPrincipal i u q) volume ∧
    (∫ q, nuclearKSRealPrincipal i φ q • u q) = ∫ q, φ q • nuclearKSPrincipal i u q := by
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
  have hL : (fun q => nuclearKSRealPrincipal i φ q • u q) =
      fun q => (∑ k : Fin 4,A k q)+(4:ℝ) • (∑ k : SpectatorCoordinate i,C k q) := by
    funext q
    simp only [nuclearKSRealPrincipal,A,C,add_smul,Finset.sum_smul,mul_smul,Finset.smul_sum]
  have hR : (fun q => φ q • nuclearKSPrincipal i u q) =
      fun q => (∑ k : Fin 4,A' k q)+(4:ℝ) • (∑ k : SpectatorCoordinate i,C' k q) := by
    funext q
    simp only [nuclearKSPrincipal,A',C',smul_add,Finset.smul_sum,mul_smul]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    exact smul_comm (φ q) (4:ℝ) _
  rw [hL,hR]
  have hLA := integrable_finsetSum Finset.univ (fun k _ => hA k)
  have hRA := integrable_finsetSum Finset.univ (fun k _ => hA' k)
  have hLC := integrable_finsetSum Finset.univ (fun k _ => hC k)
  have hRC := integrable_finsetSum Finset.univ (fun k _ => hC' k)
  have hLC4 : Integrable (fun q => (4:ℝ) • ∑ k,C k q) volume := hLC.smul (4:ℝ)
  have hRC4 : Integrable (fun q => (4:ℝ) • ∑ k,C' k q) volume := hRC.smul (4:ℝ)
  refine ⟨hLA.add hLC4,hRA.add hRC4,?_⟩
  rw [integral_add hLA hLC4,integral_add hRA hRC4,integral_smul,integral_smul,
    integral_finsetSum _ (fun k _ => hA k),integral_finsetSum _ (fun k _ => hA' k),
    integral_finsetSum _ (fun k _ => hC k),integral_finsetSum _ (fun k _ => hC' k)]
  simp only [ha,hc']

#print axioms nuclear_KS_principal_integration_by_parts
end TheoremT.Continuum
