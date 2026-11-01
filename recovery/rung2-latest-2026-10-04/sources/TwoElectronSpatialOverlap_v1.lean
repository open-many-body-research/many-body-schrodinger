import TwoElectronEigenSinglet_v1

/-! The literal hydrogen-product overlap detects every symmetric spatial
eigenvector below the actual comparison separator. No normalization is needed. -/
noncomputable section
namespace TheoremT.Continuum
open TheoremT.Polar

theorem symmetric_low_eigen_zero_of_product_overlap_zero (Z : ℝ) (hZ : 0 < Z)
    {f : SpatialL2 2} (hs : pullback twoElectronSwap f = f)
    (E : ℝ) (hE : E < -(5*Z^2/8))
    (hg : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    (horth : inner ℂ
      (twoElectronTensor (normalizedPolarGround configuration_one_finrank Z hZ)
        (normalizedPolarGround configuration_one_finrank Z hZ)) f = 0) : f = 0 := by
  let χ : FermionicSpace 2 := ⟨spinSingletLift f,spinSingletLift_fermionic f hs⟩
  have hgχ : hamiltonianGraph 2 Z χ.val (((E : ℂ) • χ).val) := by
    have h := spinSingletLift_graph hs hg
    change hamiltonianGraph 2 Z (spinSingletLift f) ((E : ℂ) • spinSingletLift f)
    simpa only [spinSingletLift_smul] using h
  let χd : (coulombPartialOperator 2 Z).domain :=
    ⟨χ,(coulombPartialOperator_domain_iff 2 Z χ).mpr ⟨(E : ℂ) • χ,hgχ⟩⟩
  have hEχ : coulombPartialOperator 2 Z χd = (E : ℂ) • χ := by
    apply Subtype.ext
    exact hamiltonian_graph_unique (coulombPartialOperator_apply_graph 2 Z χd) hgχ
  have hχorth : inner ℂ (hydrogenicSinglet Z hZ) χ = 0 := by
    change inner ℂ (twoElectronSinglet _) (spinSingletLift f) = 0
    rw [twoElectronSinglet,inner_smul_left,twoElectronRawSinglet_inner]
    have h12 := twoSpin_distinct.2.2.2.1
    simp [spinSingletLift_apply,h12,Ne.symm h12,inner_neg_right,horth]
  have hz := twoElectron_low_eigen_zero_of_overlap_zero Z hZ χd E hE hEχ hχorth
  have hz' : spinSingletLift f = 0 := congrArg Subtype.val hz
  have hn := spinSingletLift_norm_sq f
  rw [hz',norm_zero,zero_pow (by decide : 2 ≠ 0)] at hn
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg f])

theorem symmetric_low_eigen_eq_of_product_overlap_eq (Z : ℝ) (hZ : 0 < Z)
    {f g : SpatialL2 2} (hf : pullback twoElectronSwap f = f)
    (hg : pullback twoElectronSwap g = g) (E : ℝ) (hE : E < -(5*Z^2/8))
    (hfE : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f))
    (hgE : scalarHamiltonianGraph 2 Z g ((E : ℂ) • g))
    (hov : inner ℂ
      (twoElectronTensor (normalizedPolarGround configuration_one_finrank Z hZ)
        (normalizedPolarGround configuration_one_finrank Z hZ)) f =
      inner ℂ
      (twoElectronTensor (normalizedPolarGround configuration_one_finrank Z hZ)
        (normalizedPolarGround configuration_one_finrank Z hZ)) g) : f = g := by
  apply sub_eq_zero.mp
  apply symmetric_low_eigen_zero_of_product_overlap_zero Z hZ
    (by rw [map_sub,hf,hg]) E hE
  · have h := scalar_graph_add hfE (scalar_graph_smul (-1 : ℂ) hgE)
    simpa only [neg_one_smul,← sub_eq_add_neg,← smul_sub] using h
  · rw [inner_sub_right,hov,sub_self]

#print axioms symmetric_low_eigen_zero_of_product_overlap_zero
#print axioms symmetric_low_eigen_eq_of_product_overlap_eq
end TheoremT.Continuum
