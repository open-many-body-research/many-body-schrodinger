import TwoElectronTensorExchange_v1

/-! The joint spatial product projection has one-dimensional singlet range on fermions.
This file first uses the explicit unnormalized spin difference. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.Continuum

def twoSpin00 : SpinConfiguration 2 := fun _ => 0
def twoSpin01 : SpinConfiguration 2 := id
def twoSpin10 : SpinConfiguration 2 := twoElectronSwap
def twoSpin11 : SpinConfiguration 2 := fun _ => 1

theorem twoSpin_cases (σ : SpinConfiguration 2) :
    σ = twoSpin00 ∨ σ = twoSpin01 ∨ σ = twoSpin10 ∨ σ = twoSpin11 := by
  have h : ∀ σ : SpinConfiguration 2,
      σ = twoSpin00 ∨ σ = twoSpin01 ∨ σ = twoSpin10 ∨ σ = twoSpin11 := by decide
  exact h σ

theorem twoSpin_distinct : twoSpin00 ≠ twoSpin01 ∧ twoSpin00 ≠ twoSpin10 ∧
    twoSpin00 ≠ twoSpin11 ∧ twoSpin01 ≠ twoSpin10 ∧ twoSpin01 ≠ twoSpin11 ∧
    twoSpin10 ≠ twoSpin11 := by decide

theorem twoSpin_swap : permuteSpin twoElectronSwap twoSpin00 = twoSpin00 ∧
    permuteSpin twoElectronSwap twoSpin01 = twoSpin10 ∧
    permuteSpin twoElectronSwap twoSpin10 = twoSpin01 ∧
    permuteSpin twoElectronSwap twoSpin11 = twoSpin11 := by decide

theorem twoSpin_univ : (Finset.univ : Finset (SpinConfiguration 2)) =
    {twoSpin00,twoSpin01,twoSpin10,twoSpin11} := by decide

def twoElectronRawSinglet (f : SpatialL2 1) : SpinSpace 2 :=
  PiLp.single 2 twoSpin01 (twoElectronTensor f f) -
    PiLp.single 2 twoSpin10 (twoElectronTensor f f)

theorem twoElectronRawSinglet_apply (f : SpatialL2 1) (σ : SpinConfiguration 2) :
    twoElectronRawSinglet f σ =
      (if σ = twoSpin01 then twoElectronTensor f f else 0) -
        (if σ = twoSpin10 then twoElectronTensor f f else 0) := by
  simp [twoElectronRawSinglet,PiLp.single_apply]

theorem twoElectron_jointAmplitude_diagonal_zero (f : SpatialL2 1) {ψ : SpinSpace 2}
    (hψ : ψ ∈ fermionicSubspace 2) :
    inner ℂ (twoElectronTensor f f) (ψ twoSpin00) = 0 ∧
      inner ℂ (twoElectronTensor f f) (ψ twoSpin11) = 0 := by
  have h0 := twoElectron_jointAmplitude_fermionic f hψ twoElectronSwap twoSpin00
  have h1 := twoElectron_jointAmplitude_fermionic f hψ twoElectronSwap twoSpin11
  rw [twoSpin_swap.1,twoElectronSwap_sign] at h0
  rw [twoSpin_swap.2.2.2,twoElectronSwap_sign] at h1
  constructor
  · linear_combination (1/2 : ℂ) * h0
  · linear_combination (1/2 : ℂ) * h1

theorem twoElectron_jointAmplitude_offdiagonal (f : SpatialL2 1) {ψ : SpinSpace 2}
    (hψ : ψ ∈ fermionicSubspace 2) :
    inner ℂ (twoElectronTensor f f) (ψ twoSpin10) =
      -inner ℂ (twoElectronTensor f f) (ψ twoSpin01) := by
  have h := twoElectron_jointAmplitude_fermionic f hψ twoElectronSwap twoSpin01
  simpa only [twoSpin_swap.2.1,twoElectronSwap_sign,neg_one_mul] using h

theorem twoElectron_jointProjection_rawSinglet (f : SpatialL2 1) {ψ : SpinSpace 2}
    (hψ : ψ ∈ fermionicSubspace 2) :
    twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ) =
      inner ℂ (twoElectronTensor f f) (ψ twoSpin01) • twoElectronRawSinglet f := by
  rcases twoSpin_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  have hd := twoElectron_jointAmplitude_diagonal_zero f hψ
  have ho := twoElectron_jointAmplitude_offdiagonal f hψ
  apply (WithLp.ext_iff 2).mpr
  funext σ
  change twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ) σ =
    inner ℂ (twoElectronTensor f f) (ψ twoSpin01) • twoElectronRawSinglet f σ
  rw [twoElectronSpinProjectFirstSecond_apply,twoElectronRawSinglet_apply]
  rcases twoSpin_cases σ with rfl | rfl | rfl | rfl <;>
    simp [h01,h02,h03,h12,h13,h23,Ne.symm h01,Ne.symm h02,Ne.symm h03,
      Ne.symm h12,Ne.symm h13,Ne.symm h23,hd.1,hd.2,ho]

theorem twoElectronRawSinglet_fermionic (f : SpatialL2 1) :
    twoElectronRawSinglet f ∈ fermionicSubspace 2 := by
  rcases twoSpin_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  intro π σ
  rcases twoElectron_permutation_cases π with rfl | rfl
  · have hs : permuteSpin (1 : Equiv.Perm (Fin 2)) σ = σ := rfl
    rw [hs,pullback_one,permutationSign_one,one_smul]
  · rcases twoSpin_cases σ with rfl | rfl | rfl | rfl <;>
      simp [twoSpin_swap.1,twoSpin_swap.2.1,twoSpin_swap.2.2.1,twoSpin_swap.2.2.2,
        twoElectronRawSinglet_apply,twoElectronSwap_sign,twoElectronTensor_swap,
        h01,h02,h03,h12,h13,h23,Ne.symm h01,Ne.symm h02,Ne.symm h03,
        Ne.symm h12,Ne.symm h13,Ne.symm h23]

theorem twoElectronRawSinglet_norm_sq (f : SpatialL2 1) :
    ‖twoElectronRawSinglet f‖ ^ 2 = 2 * ‖f‖ ^ 4 := by
  rcases twoSpin_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  rw [PiLp.norm_sq_eq_of_L2,twoSpin_univ]
  simp [twoElectronRawSinglet_apply,twoElectronTensor_norm,
    h01,h02,h03,h12,h13,h23,Ne.symm h01,Ne.symm h02,Ne.symm h03,
    Ne.symm h12,Ne.symm h13,Ne.symm h23]
  ring

theorem twoElectron_jointProjection_mem_singlet_span (f : SpatialL2 1) {ψ : SpinSpace 2}
    (hψ : ψ ∈ fermionicSubspace 2) :
    twoElectronSpinProjectFirst f (twoElectronSpinProjectSecond f ψ) ∈
      Submodule.span ℂ {twoElectronRawSinglet f} := by
  rw [twoElectron_jointProjection_rawSinglet f hψ]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

#print axioms twoElectron_jointProjection_rawSinglet
#print axioms twoElectronRawSinglet_fermionic
#print axioms twoElectronRawSinglet_norm_sq
#print axioms twoElectron_jointProjection_mem_singlet_span
end TheoremT.Continuum
