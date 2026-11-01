import PhysicalSpinSinglet_v1
import TwoElectronPhysicalGroundBranch_v1

/-! Every actual two-electron eigenvector below the comparison separator has
singlet spin and symmetric spatial amplitude. No positivity hypothesis is used. -/
noncomputable section
namespace TheoremT.Continuum

theorem spinSingletLift_hydrogen_inner (f : SpatialL2 1) (ψ : SpinSpace 2) :
    inner ℂ (twoElectronSinglet f) (spinSingletLift (spinSingletDifference ψ)) =
      (2 : ℂ) * inner ℂ (twoElectronSinglet f) ψ := by
  have h12 := twoSpin_distinct.2.2.2.1
  simp only [twoElectronSinglet,inner_smul_left,twoElectronRawSinglet_inner,
    spinSingletLift_apply,ite_true,if_neg h12,if_neg (Ne.symm h12),sub_zero,
    zero_sub,inner_neg_right,spinSingletDifference,inner_sub_right]
  ring

theorem twoElectron_low_eigen_zero_of_overlap_zero (Z : ℝ) (hZ : 0 < Z)
    (u : (coulombPartialOperator 2 Z).domain) (E : ℝ) (hE : E < -(5*Z^2/8))
    (hEu : coulombPartialOperator 2 Z u = (E : ℂ) • (u : FermionicSpace 2))
    (horth : inner ℂ (hydrogenicSinglet Z hZ) (u : FermionicSpace 2) = 0) :
    (u : FermionicSpace 2) = 0 := by
  have h := twoElectron_operator_rank_one Z hZ u
  have he : (inner ℂ (u : FermionicSpace 2) (coulombPartialOperator 2 Z u)).re =
      E * ‖(u : FermionicSpace 2)‖^2 := by
    rw [hEu]
    change (inner ℂ (u : FermionicSpace 2).val
      ((E : ℂ) • (u : FermionicSpace 2).val)).re = E * ‖(u : FermionicSpace 2).val‖^2
    rw [inner_smul_right,inner_self_eq_norm_sq_to_K]
    simp [← Complex.ofReal_pow]
  rw [he,horth,norm_zero,zero_pow (by decide : 2 ≠ 0),mul_zero,add_zero] at h
  apply norm_eq_zero.mp
  by_contra hn
  exact hE.not_ge ((mul_le_mul_iff_of_pos_right (sq_pos_of_ne_zero hn)).mp h)

theorem twoElectron_low_eigen_singlet (Z : ℝ) (hZ : 0 < Z)
    (g : (coulombPartialOperator 2 Z).domain) (E : ℝ) (hE : E < -(5*Z^2/8))
    (hEg : coulombPartialOperator 2 Z g = (E : ℂ) • (g : FermionicSpace 2)) :
    (2 : ℂ) • (g : FermionicSpace 2).val =
      spinSingletLift (spinSingletDifference (g : FermionicSpace 2).val) := by
  let F := spinSingletDifference (g : FermionicSpace 2).val
  have hgraph := coulombPartialOperator_apply_graph 2 Z g
  have hscalar : scalarHamiltonianGraph 2 Z F ((E : ℂ) • F) := by
    have h := spinSingletDifference_graph hgraph
    rw [hEg] at h
    exact (spinSingletDifference_smul (E : ℂ) (g : FermionicSpace 2).val) ▸ h
  have hF := spinSingletDifference_swap (g : FermionicSpace 2).property
  let χ : FermionicSpace 2 := ⟨spinSingletLift F,spinSingletLift_fermionic F hF⟩
  have hgχ : hamiltonianGraph 2 Z χ.val (((E : ℂ) • χ).val) := by
    have h := spinSingletLift_graph hF hscalar
    change hamiltonianGraph 2 Z (spinSingletLift F) ((E : ℂ) • spinSingletLift F)
    simpa only [spinSingletLift_smul] using h
  let χd : (coulombPartialOperator 2 Z).domain :=
    ⟨χ,(coulombPartialOperator_domain_iff 2 Z χ).mpr ⟨(E : ℂ) • χ,hgχ⟩⟩
  have hEχ : coulombPartialOperator 2 Z χd = (E : ℂ) • χ := by
    apply Subtype.ext
    exact hamiltonian_graph_unique (coulombPartialOperator_apply_graph 2 Z χd) hgχ
  let w : (coulombPartialOperator 2 Z).domain := (2 : ℂ) • g - χd
  have hEw : coulombPartialOperator 2 Z w = (E : ℂ) • (w : FermionicSpace 2) := by
    simp only [w,(coulombPartialOperator 2 Z).map_sub,
      (coulombPartialOperator 2 Z).map_smul,hEg,hEχ,Submodule.coe_sub,Submodule.coe_smul]
    change (2 : ℂ) • ((E : ℂ) • (g : FermionicSpace 2)) - (E : ℂ) • χ =
      (E : ℂ) • ((2 : ℂ) • (g : FermionicSpace 2) - χ)
    module
  have hw : inner ℂ (hydrogenicSinglet Z hZ) (w : FermionicSpace 2) = 0 := by
    change inner ℂ (twoElectronSinglet _) ((2 : ℂ) • (g : FermionicSpace 2).val - spinSingletLift F) = 0
    rw [inner_sub_right,inner_smul_right]
    change (2 : ℂ) * inner ℂ (twoElectronSinglet _) (g : FermionicSpace 2).val -
      inner ℂ (twoElectronSinglet _) (spinSingletLift (spinSingletDifference (g : FermionicSpace 2).val)) = 0
    rw [spinSingletLift_hydrogen_inner,sub_self]
  have hz := twoElectron_low_eigen_zero_of_overlap_zero Z hZ w E hE hEw hw
  have hs : (2 : ℂ) • (g : FermionicSpace 2) - χ = 0 := hz
  exact congrArg Subtype.val (sub_eq_zero.mp hs)

#print axioms twoElectron_low_eigen_singlet
end TheoremT.Continuum
