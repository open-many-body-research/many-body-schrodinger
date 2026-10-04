import TwoElectronEigenSinglet_v1

/-! Actual normalized symmetric spatial H² eigenfunctions, obtained from the
physical fermionic ground state. Realness, rotation invariance and decay are separate. -/
noncomputable section
namespace TheoremT.Continuum

theorem twoElectron_low_eigen_spatial_amplitude (Z : ℝ) (hZ : 0 < Z)
    (g : (coulombPartialOperator 2 Z).domain) (hg : ‖(g : FermionicSpace 2)‖ = 1)
    (E : ℝ) (hE : E < -(5*Z^2/8))
    (hEg : coulombPartialOperator 2 Z g = (E : ℂ) • (g : FermionicSpace 2)) :
    ∃ u : SpatialL2 2, ‖u‖ = 1 ∧ pullback twoElectronSwap u = u ∧ HasH2 u ∧
      scalarHamiltonianGraph 2 Z u ((E : ℂ) • u) ∧
      (g : FermionicSpace 2).val = ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ • spinSingletLift u := by
  let F := spinSingletDifference (g : FermionicSpace 2).val
  let c : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)⁻¹
  have hF := spinSingletDifference_swap (g : FermionicSpace 2).property
  have hscalar : scalarHamiltonianGraph 2 Z F ((E : ℂ) • F) := by
    have h := spinSingletDifference_graph (coulombPartialOperator_apply_graph 2 Z g)
    rw [hEg] at h
    exact (spinSingletDifference_smul (E : ℂ) (g : FermionicSpace 2).val) ▸ h
  have hs := twoElectron_low_eigen_singlet Z hZ g E hE hEg
  have hF2 : ‖F‖^2 = 2 := by
    have hn := congrArg (fun ψ : SpinSpace 2 => ‖ψ‖^2) hs
    rw [norm_smul,mul_pow,spinSingletLift_norm_sq] at hn
    have hgn : ‖(g : FermionicSpace 2).val‖ = 1 := hg
    rw [hgn] at hn
    norm_num at hn
    dsimp only [F]
    linarith
  have hc2 : ‖c‖^2 = (1/2 : ℝ) := by
    dsimp [c]
    rw [norm_inv,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg 2),inv_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hu : ‖c • F‖ = 1 := by
    have hn : ‖c • F‖^2 = 1 := by rw [norm_smul,mul_pow,hc2,hF2];norm_num
    nlinarith [norm_nonneg (c • F)]
  have hgu : scalarHamiltonianGraph 2 Z (c • F) ((E : ℂ) • (c • F)) := by
    have h := scalar_graph_smul c hscalar
    rwa [smul_comm c (E : ℂ) F] at h
  refine ⟨c • F,hu,?_,scalar_graph_hasH2 hgu,hgu,?_⟩
  · rw [map_smul,hF]
  · have hsqrt : ((Real.sqrt 2 : ℝ) : ℂ)^2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    have hc : c*c = (1/2 : ℂ) := by
      dsimp [c]
      rw [← pow_two,inv_pow,hsqrt]
      norm_num
    change (g : FermionicSpace 2).val = c • spinSingletLift (c • F)
    rw [spinSingletLift_smul,smul_smul,hc,← hs,smul_smul]
    norm_num

theorem twoElectron_ground_spatial_eigenfunction (Z : ℝ) (hZ : 0 < Z)
    (hsep : 32 < 9*Z^2) :
    ∃ u : SpatialL2 2, ‖u‖ = 1 ∧ pullback twoElectronSwap u = u ∧ HasH2 u ∧
      scalarHamiltonianGraph 2 Z u (((variationalGroundEnergy 2 Z).toReal : ℂ) • u) := by
  obtain ⟨hE,g,hg,hEg,_,_⟩ := twoElectron_physical_ground_branch Z hZ hsep
  obtain ⟨u,hu,hs,hH2,hgraph,_⟩ := twoElectron_low_eigen_spatial_amplitude Z hZ g hg _ hE hEg
  exact ⟨u,hu,hs,hH2,hgraph⟩

#print axioms twoElectron_low_eigen_spatial_amplitude
#print axioms twoElectron_ground_spatial_eigenfunction
end TheoremT.Continuum
