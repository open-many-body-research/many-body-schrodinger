import ConfigurationIsometryH2_v1
import FreeResolvent_v1

/-! Exact weak Coulomb-graph covariance under orthogonal maps preserving the
actual potential. The potential invariance hypothesis is explicit; physical
simultaneous rotations will discharge it separately. -/
noncomputable section
open MeasureTheory
open scoped SchwartzMap Laplacian BigOperators
namespace TheoremT.Continuum

theorem scalar_graph_configurationIsometryPull {N : ℕ} {Z : ℝ}
    (U : Configuration N ≃ₗᵢ[ℝ] Configuration N)
    (hV : ∀ x, coulombPotential N Z (U x) = coulombPotential N Z x)
    {f h : SpatialL2 N} (hg : scalarHamiltonianGraph N Z f h) :
    scalarHamiltonianGraph N Z (configurationIsometryPull U f)
      (configurationIsometryPull U h) := by
  classical
  have hfU := (scalar_graph_hasH2 hg).configurationIsometryPull U
  obtain ⟨d,e,hd,he,hout⟩ := hg
  obtain ⟨d',hd',he'⟩ := hfU
  choose e' he' using he'
  have hsum : (∑ k, e' k k) = configurationIsometryPull U (∑ k, e k k) := by
    apply spatialL2_toTemperedDistribution_injective N
    exact (distribution_laplacian_eq_sum_of_weakPartial d' (fun k => e' k k)
      hd' (fun k => he' k k)).symm.trans
      (configurationIsometryPull_laplacian U f (∑ k, e k k)
        (distribution_laplacian_eq_sum_of_weakPartial d (fun k => e k k)
          hd (fun k => he k k)))
  refine ⟨d',e',hd',he',?_⟩
  have ha := Lp.coeFn_fun_finsetSum Finset.univ (fun k => e' k k)
  have hb := U.measurePreserving.quasiMeasurePreserving.ae
    (Lp.coeFn_fun_finsetSum Finset.univ (fun k => e k k))
  have hc := configurationIsometryPull_ae U (∑ k, e k k)
  rw [← hsum] at hc
  have ht := U.measurePreserving.quasiMeasurePreserving.ae hout
  filter_upwards [ha,hb,hc,ht,configurationIsometryPull_ae U f,
    configurationIsometryPull_ae U h] with x hax hbx hcx htx hfx hhx
  simp only [Function.comp_apply,Finset.sum_apply] at *
  rw [hhx,hfx,htx,hV]
  rw [hax,hbx] at hcx
  rw [hcx]

#print axioms scalar_graph_configurationIsometryPull
end TheoremT.Continuum
