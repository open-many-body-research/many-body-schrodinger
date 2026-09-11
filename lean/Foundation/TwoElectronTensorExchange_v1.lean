import TwoElectronSpinProjection_v1
import FermionicAction_v2

/-! Actual spatial exchange of two-electron products and joint fermionic invariance. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

def twoElectronSwap : Equiv.Perm (Fin 2) := Equiv.swap 0 1

theorem twoElectron_permutation_cases (π : Equiv.Perm (Fin 2)) :
    π = 1 ∨ π = twoElectronSwap := by
  have h : ∀ π : Equiv.Perm (Fin 2), π = 1 ∨ π = twoElectronSwap := by decide
  exact h π

theorem twoElectronSwap_sign : permutationSign twoElectronSwap = -1 := by
  simp [twoElectronSwap,permutationSign]

theorem twoElectronConfigurationProduct_swap (q : Configuration 2) :
    twoElectronConfigurationProduct (permuteSpace twoElectronSwap q) =
      (twoElectronConfigurationProduct q).swap := by
  apply Prod.ext
  · apply (WithLp.ext_iff 2).mpr
    funext k
    rcases k with ⟨i,k⟩
    fin_cases i
    change q (twoElectronSwap 0,k) = q (1,k)
    simp [twoElectronSwap]
  · apply (WithLp.ext_iff 2).mpr
    funext k
    rcases k with ⟨i,k⟩
    fin_cases i
    change q (twoElectronSwap 1,k) = q (0,k)
    simp [twoElectronSwap]

theorem twoElectronTensor_swap (f g : SpatialL2 1) :
    pullback twoElectronSwap (twoElectronTensor f g) = twoElectronTensor g f := by
  apply Lp.ext
  have ht := (permuteSpace twoElectronSwap).measurePreserving.quasiMeasurePreserving.ae
    (twoElectronTensor_ae f g)
  filter_upwards [pullback_ae twoElectronSwap (twoElectronTensor f g),ht,
    twoElectronTensor_ae g f] with q hp ht hgf
  simp only [Function.comp_apply] at hp
  rw [hp,ht,twoElectronConfigurationProduct_swap,hgf]
  exact mul_comm _ _

theorem twoElectronTensor_self_permutation (f : SpatialL2 1) (π : Equiv.Perm (Fin 2)) :
    pullback π (twoElectronTensor f f) = twoElectronTensor f f := by
  rcases twoElectron_permutation_cases π with rfl | rfl
  · exact pullback_one _ _
  · exact twoElectronTensor_swap f f

theorem pullback_inner_preserved {N : ℕ} (π : Equiv.Perm (Fin N)) (f g : SpatialL2 N) :
    inner ℂ (pullback π f) (pullback π g) = inner ℂ f g :=
  (Lp.compMeasurePreservingₗᵢ ℂ (permuteSpace π) (permuteSpace π).measurePreserving).inner_map_map f g

theorem twoElectron_jointAmplitude_fermionic (f : SpatialL2 1) {ψ : SpinSpace 2}
    (hψ : ψ ∈ fermionicSubspace 2) (π : Equiv.Perm (Fin 2)) (σ : SpinConfiguration 2) :
    inner ℂ (twoElectronTensor f f) (ψ (permuteSpin π σ)) =
      permutationSign π * inner ℂ (twoElectronTensor f f) (ψ σ) := by
  rw [← pullback_inner_preserved π,twoElectronTensor_self_permutation,hψ π σ,
    inner_smul_right]

theorem twoElectron_jointProjection_fermionic (f : SpatialL2 1) {ψ : SpinSpace 2}
    (hψ : ψ ∈ fermionicSubspace 2) :
    twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ) ∈ fermionicSubspace 2 := by
  intro π σ
  rw [twoElectronSpinProjectFirstSecond_apply,twoElectronSpinProjectFirstSecond_apply,
    map_smul,twoElectronTensor_self_permutation,twoElectron_jointAmplitude_fermionic f hψ,
    smul_smul]

#print axioms twoElectron_permutation_cases
#print axioms twoElectronTensor_swap
#print axioms twoElectron_jointAmplitude_fermionic
#print axioms twoElectron_jointProjection_fermionic
end TheoremT.Continuum
