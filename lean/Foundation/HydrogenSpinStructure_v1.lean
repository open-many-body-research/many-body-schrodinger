import HydrogenRadialNorm_v1
import FermionicAction_v2
import CoulombOperatorCore_v2
import Mathlib.LinearAlgebra.Pi

/-! One-electron spin packaging in the full simultaneous-permutation space.
The spin map is injective for every nonzero spatial L2 vector. The graph
transport theorem is an explicitly conditional structural implication. -/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace TheoremT.Continuum

theorem one_electron_all_spin_fermionic (ψ : SpinSpace 1) :
    ψ ∈ fermionicSubspace 1 := by
  intro π σ
  have hp : π = 1 := Subsingleton.elim _ _
  subst π
  have hs : permuteSpin (1 : Equiv.Perm (Fin 1)) σ = σ := by
    funext i
    rfl
  rw [hs, permutationSign_one, one_smul]
  exact pullback_one 1 (ψ σ)

def oneElectronSpinMap (f : SpatialL2 1) : (Fin 2 → ℂ) →ₗ[ℂ] SpinSpace 1 where
  toFun c := WithLp.toLp 2 (fun σ => c (σ 0) • f)
  map_add' c d := by
    apply (WithLp.ext_iff 2).mpr
    funext σ
    exact add_smul _ _ _
  map_smul' c d := by
    apply (WithLp.ext_iff 2).mpr
    funext σ
    exact mul_smul _ _ _

@[simp] theorem oneElectronSpinMap_apply (f : SpatialL2 1) (c : Fin 2 → ℂ)
    (σ : SpinConfiguration 1) : oneElectronSpinMap f c σ = c (σ 0) • f := rfl

theorem oneElectronSpinMap_injective {f : SpatialL2 1} (hf : f ≠ 0) :
    Function.Injective (oneElectronSpinMap f) := by
  intro c d h
  funext j
  apply smul_left_injective ℂ hf
  exact congrArg (fun ψ : SpinSpace 1 => ψ (fun _ => j)) h

theorem oneElectronSpinMap_graph {Z : ℝ} {f h : SpatialL2 1}
    (hg : scalarHamiltonianGraph 1 Z f h) (c : Fin 2 → ℂ) :
    hamiltonianGraph 1 Z (oneElectronSpinMap f c) (oneElectronSpinMap h c) := by
  exact ⟨one_electron_all_spin_fermionic _, one_electron_all_spin_fermionic _,
    fun σ => scalar_graph_smul (c (σ 0)) hg⟩

theorem oneElectronSpinMap_eigen_graph {Z : ℝ} {f : SpatialL2 1} {e : ℂ}
    (hg : scalarHamiltonianGraph 1 Z f (e • f)) (c : Fin 2 → ℂ) :
    hamiltonianGraph 1 Z (oneElectronSpinMap f c) (e • oneElectronSpinMap f c) := by
  have he : oneElectronSpinMap (e • f) c = e • oneElectronSpinMap f c := by
    apply (WithLp.ext_iff 2).mpr
    funext σ
    exact smul_comm _ _ _
  rw [← he]
  exact oneElectronSpinMap_graph hg c

def hydrogenSpinMap (Z : ℝ) (hZ : 0 < Z) : (Fin 2 → ℂ) →ₗ[ℂ] SpinSpace 1 :=
  oneElectronSpinMap (hydrogenRadialL2 Z hZ)

theorem hydrogenSpinMap_injective (Z : ℝ) (hZ : 0 < Z) :
    Function.Injective (hydrogenSpinMap Z hZ) :=
  oneElectronSpinMap_injective (hydrogenRadialL2_ne_zero Z hZ)

theorem hydrogenSpinMap_nonzero (Z : ℝ) (hZ : 0 < Z) {c : Fin 2 → ℂ} (hc : c ≠ 0) :
    hydrogenSpinMap Z hZ c ≠ 0 := by
  intro he
  apply hc
  exact hydrogenSpinMap_injective Z hZ (by simpa using he)

theorem hydrogenSpinMap_two_independent (Z : ℝ) (hZ : 0 < Z) :
    LinearIndependent ℂ (fun j : Fin 2 => hydrogenSpinMap Z hZ (Pi.basisFun ℂ (Fin 2) j)) := by
  exact (Pi.basisFun ℂ (Fin 2)).linearIndependent.map'
    (hydrogenSpinMap Z hZ) (LinearMap.ker_eq_bot.mpr (hydrogenSpinMap_injective Z hZ))

end TheoremT.Continuum
