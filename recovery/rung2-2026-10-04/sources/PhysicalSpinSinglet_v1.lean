import TwoElectronSingletForm_v1
import FermionicGraphAssembly_v2

/-! The actual spin singlet lift of any symmetric two-electron spatial L² vector.
This generalizes the auxiliary repeated hydrogen product without changing it. -/
noncomputable section
namespace TheoremT.Continuum

def spinSingletLift (F : SpatialL2 2) : SpinSpace 2 :=
  PiLp.single 2 twoSpin01 F - PiLp.single 2 twoSpin10 F

theorem spinSingletLift_apply (F : SpatialL2 2) (σ : SpinConfiguration 2) :
    spinSingletLift F σ = (if σ = twoSpin01 then F else 0) -
      (if σ = twoSpin10 then F else 0) := by
  simp [spinSingletLift,PiLp.single_apply]

theorem spinSingletLift_weight (F : SpatialL2 2) (σ : SpinConfiguration 2) :
    spinSingletLift F σ = twoElectronSingletSpinWeight σ • F := by
  rw [spinSingletLift_apply]
  unfold twoElectronSingletSpinWeight
  split_ifs <;> simp

theorem spinSingletLift_smul (c : ℂ) (F : SpatialL2 2) :
    spinSingletLift (c • F) = c • spinSingletLift F := by
  apply (WithLp.ext_iff 2).mpr
  funext σ
  change spinSingletLift (c • F) σ = c • spinSingletLift F σ
  rw [spinSingletLift_weight,spinSingletLift_weight,smul_comm]

theorem spinSingletLift_fermionic (F : SpatialL2 2)
    (hF : pullback twoElectronSwap F = F) :
    spinSingletLift F ∈ fermionicSubspace 2 := by
  rcases twoSpin_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  intro π σ
  rcases twoElectron_permutation_cases π with rfl | rfl
  · have hs : permuteSpin (1 : Equiv.Perm (Fin 2)) σ = σ := rfl
    rw [hs,pullback_one,permutationSign_one,one_smul]
  · rcases twoSpin_cases σ with rfl | rfl | rfl | rfl <;>
      simp [twoSpin_swap.1,twoSpin_swap.2.1,twoSpin_swap.2.2.1,twoSpin_swap.2.2.2,
        spinSingletLift_apply,twoElectronSwap_sign,hF,
        h01,h02,h03,h12,h13,h23,Ne.symm h01,Ne.symm h02,Ne.symm h03,
        Ne.symm h12,Ne.symm h13,Ne.symm h23]

theorem spinSingletLift_graph {Z : ℝ} {F K : SpatialL2 2}
    (hF : pullback twoElectronSwap F = F) (hgraph : scalarHamiltonianGraph 2 Z F K) :
    hamiltonianGraph 2 Z (spinSingletLift F) (spinSingletLift K) := by
  have hin := spinSingletLift_fermionic F hF
  have hs : ∀ σ, scalarHamiltonianGraph 2 Z (spinSingletLift F σ) (spinSingletLift K σ) := by
    intro σ
    rw [spinSingletLift_weight,spinSingletLift_weight]
    exact scalar_graph_smul _ hgraph
  exact ⟨hin,scalar_outputs_fermionic hin hs,hs⟩

theorem spinSingletLift_inner (F : SpatialL2 2) (ψ : SpinSpace 2) :
    inner ℂ (spinSingletLift F) ψ =
      inner ℂ F (ψ twoSpin01) - inner ℂ F (ψ twoSpin10) := by
  rcases twoSpin_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  rw [PiLp.inner_apply,twoSpin_univ]
  simp [spinSingletLift_apply,h01,h02,h03,h12,h13,h23,
    Ne.symm h12,Ne.symm h13,Ne.symm h23,sub_eq_add_neg]

theorem spinSingletLift_norm_sq (F : SpatialL2 2) :
    ‖spinSingletLift F‖^2 = 2 * ‖F‖^2 := by
  rcases twoSpin_distinct with ⟨h01,h02,h03,h12,h13,h23⟩
  rw [PiLp.norm_sq_eq_of_L2,twoSpin_univ]
  simp [spinSingletLift_apply,h01,h02,h03,h12,h13,h23,
    Ne.symm h12,Ne.symm h13,Ne.symm h23]
  ring

def spinSingletDifference (ψ : SpinSpace 2) : SpatialL2 2 :=
  ψ twoSpin01 - ψ twoSpin10

theorem spinSingletDifference_swap {ψ : SpinSpace 2}
    (hψ : ψ ∈ fermionicSubspace 2) :
    pullback twoElectronSwap (spinSingletDifference ψ) = spinSingletDifference ψ := by
  have h01 := hψ twoElectronSwap twoSpin01
  have h10 := hψ twoElectronSwap twoSpin10
  rw [twoSpin_swap.2.1,twoElectronSwap_sign] at h01
  rw [twoSpin_swap.2.2.1,twoElectronSwap_sign] at h10
  rw [spinSingletDifference,map_sub,h10,h01]
  simp only [neg_one_smul]
  abel

theorem spinSingletDifference_graph {Z : ℝ} {ψ K : SpinSpace 2}
    (hgraph : hamiltonianGraph 2 Z ψ K) :
    scalarHamiltonianGraph 2 Z (spinSingletDifference ψ) (spinSingletDifference K) := by
  have h := scalar_graph_add (hgraph.2.2 twoSpin01)
    (scalar_graph_smul (-1) (hgraph.2.2 twoSpin10))
  simpa only [spinSingletDifference,neg_one_smul,sub_eq_add_neg] using h

theorem spinSingletDifference_smul (c : ℂ) (ψ : SpinSpace 2) :
    spinSingletDifference (c • ψ) = c • spinSingletDifference ψ := by
  change c • ψ twoSpin01 - c • ψ twoSpin10 = c • (ψ twoSpin01 - ψ twoSpin10)
  rw [smul_sub]

#print axioms spinSingletLift_graph
#print axioms spinSingletDifference_graph
end TheoremT.Continuum
