import CoulombConjugation_v1
import TwoElectronGroundSpatial_v1

/-! A real normalized symmetric spatial H² eigenfunction at the actual
fermionic ground energy. Positivity, rotation invariance and decay are not asserted. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum

theorem symmetric_eigen_has_real_nonzero {Z E : ℝ} {f : SpatialL2 2}
    (hf : f ≠ 0) (hs : pullback twoElectronSwap f = f)
    (hg : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f)) :
    ∃ w : SpatialL2 2, w ≠ 0 ∧ spatialConj w = w ∧
      pullback twoElectronSwap w = w ∧ scalarHamiltonianGraph 2 Z w ((E : ℂ) • w) := by
  have hgc := scalar_graph_conj hg
  rw [spatialConj_smul,Complex.conj_ofReal] at hgc
  by_cases hw : f + spatialConj f = 0
  · have hcf : spatialConj f = -f := by
      calc
        spatialConj f = (f + spatialConj f) - f := by abel
        _ = -f := by rw [hw,zero_sub]
    refine ⟨Complex.I • f,smul_ne_zero Complex.I_ne_zero hf,?_,?_,?_⟩
    · simp [spatialConj_smul,hcf]
    · rw [map_smul,hs]
    · have h := scalar_graph_smul Complex.I hg
      rwa [smul_comm Complex.I (E : ℂ) f] at h
  · refine ⟨f + spatialConj f,hw,?_,?_,?_⟩
    · rw [map_add,spatialConj_involutive,add_comm]
    · rw [map_add,← spatialConj_pullback,hs]
    · have h := scalar_graph_add hg hgc
      rwa [← smul_add] at h

theorem symmetric_eigen_has_real_unit {Z E : ℝ} {f : SpatialL2 2}
    (hf : f ≠ 0) (hs : pullback twoElectronSwap f = f)
    (hg : scalarHamiltonianGraph 2 Z f ((E : ℂ) • f)) :
    ∃ u : SpatialL2 2, ‖u‖ = 1 ∧ pullback twoElectronSwap u = u ∧ HasH2 u ∧
      scalarHamiltonianGraph 2 Z u ((E : ℂ) • u) ∧ ∀ᵐ x, (u x).im = 0 := by
  obtain ⟨w,hw,hc,hws,hwg⟩ := symmetric_eigen_has_real_nonzero hf hs hg
  let r : ℝ := ‖w‖⁻¹
  have hnorm : ‖(r : ℂ) • w‖ = 1 := by
    rw [norm_smul,Complex.norm_real]
    dsimp [r]
    rw [abs_inv,abs_of_nonneg (norm_nonneg w),inv_mul_cancel₀ (norm_ne_zero_iff.mpr hw)]
  have hgraph : scalarHamiltonianGraph 2 Z ((r : ℂ) • w) ((E : ℂ) • ((r : ℂ) • w)) := by
    have h := scalar_graph_smul (r : ℂ) hwg
    rwa [smul_comm (r : ℂ) (E : ℂ) w] at h
  refine ⟨(r : ℂ) • w,hnorm,?_,scalar_graph_hasH2 hgraph,hgraph,?_⟩
  · rw [map_smul,hws]
  · apply spatialConj_fixed_im_zero
    rw [spatialConj_smul,Complex.conj_ofReal,hc]

theorem twoElectron_ground_real_spatial_eigenfunction (Z : ℝ) (hZ : 0 < Z)
    (hsep : 32 < 9*Z^2) :
    ∃ u : SpatialL2 2, ‖u‖ = 1 ∧ pullback twoElectronSwap u = u ∧ HasH2 u ∧
      scalarHamiltonianGraph 2 Z u (((variationalGroundEnergy 2 Z).toReal : ℂ) • u) ∧
      ∀ᵐ x, (u x).im = 0 := by
  obtain ⟨f,hf,hs,_,hg⟩ := twoElectron_ground_spatial_eigenfunction Z hZ hsep
  have hne : f ≠ 0 := by intro h;rw [h,norm_zero] at hf;norm_num at hf
  exact symmetric_eigen_has_real_unit hne hs hg

#print axioms twoElectron_ground_real_spatial_eigenfunction
end TheoremT.Continuum
