import HardyFermionicFreeResolvent_v1
import HardyCoulombSymmetry_v2
import SpinCoulombNorm_v2

/-! Identification of the actual Coulomb perturbation on the positive free
resolvent range, without a separate assumption about fermionic covariance. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem positiveFreeGraph_coulomb_error_eq {N : ℕ} {μ Z : ℝ}
    {u f h v : SpatialL2 N} (hfree : positiveFreeGraph μ u f)
    (hcoul : scalarHamiltonianGraph N Z u h)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ)*u x) :
    h + (μ : ℂ)•u - f = v := by
  obtain ⟨d,e,hd,he,hout⟩ := hfree
  obtain ⟨dc,ec,hdc,hec,hcout⟩ := hcoul
  have hdeq : dc=d := funext (fun k => weakPartial_unique (hdc k) (hd k))
  subst dc
  have heeq : ec=e := funext (fun k => funext (fun l => weakPartial_unique (hec k l) (he k l)))
  subst ec
  rw [scalar_graph_value_decomposition e hcout hv,hout,spatialL2_complex_ofReal_smul]
  have hk : (-((1:ℂ)/2)) • (∑ k : Coordinate N, e k k) =
      (-1/2:ℝ) • (∑ k : Coordinate N, e k k) := by
    convert spatialL2_complex_ofReal_smul N (-1/2:ℝ) (∑ k : Coordinate N, e k k) using 1 <;> norm_num
  rw [hk]
  abel

theorem positiveFreeGraph_coulomb_error_ae {N : ℕ} {μ Z : ℝ}
    {u f h : SpatialL2 N} (hfree : positiveFreeGraph μ u f)
    (hcoul : scalarHamiltonianGraph N Z u h) :
    (h + (μ : ℂ)•u - f : SpatialL2 N) =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ)*u x := by
  have hv := coulombProductL2_of_scalar_graph hcoul
  rw [positiveFreeGraph_coulomb_error_eq hfree hcoul hv.coeFn_toLp]
  exact hv.coeFn_toLp

theorem fermionicFreeResolvent_mem_domain (N : ℕ) (Z : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) : fermionicFreeResolvent N μ hμ ψ ∈ (coulombPartialOperator N Z).domain := by
  rw [coulombPartialOperator_domain_iff_H2]
  exact (fermionicFreeResolvent_hasH2 N hμ ψ).2

def fermionicFreeResolventToDomain (N : ℕ) (Z : ℝ) (μ : ℝ) (hμ : 0 < μ) :
    FermionicSpace N →ₗ[ℂ] (coulombPartialOperator N Z).domain :=
  (fermionicFreeResolvent N μ hμ).toLinearMap.codRestrict _
    (fermionicFreeResolvent_mem_domain N Z hμ)

def coulombFreeErrorLinear (N : ℕ) (Z μ : ℝ) (hμ : 0 < μ) :
    FermionicSpace N →ₗ[ℂ] FermionicSpace N :=
  (coulombPartialOperator N Z).toFun.comp (fermionicFreeResolventToDomain N Z μ hμ) +
    (μ : ℂ) • (fermionicFreeResolvent N μ hμ).toLinearMap - LinearMap.id

theorem coulombFreeErrorLinear_apply_ae (N : ℕ) (Z : ℝ) {μ : ℝ} (hμ : 0 < μ)
    (ψ : FermionicSpace N) (σ : SpinConfiguration N) :
    (coulombFreeErrorLinear N Z μ hμ ψ).val σ =ᵐ[volume]
      fun x => (coulombPotential N Z x : ℂ)*(fermionicFreeResolvent N μ hμ ψ).val σ x := by
  exact positiveFreeGraph_coulomb_error_ae (fermionicFreeResolvent_solve N hμ ψ σ)
    ((coulombPartialOperator_apply_graph N Z (fermionicFreeResolventToDomain N Z μ hμ ψ)).2.2 σ)

#print axioms positiveFreeGraph_coulomb_error_eq
#print axioms coulombFreeErrorLinear_apply_ae
end TheoremT.Continuum
