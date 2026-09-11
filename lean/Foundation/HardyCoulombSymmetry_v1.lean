import HardyWeakLaplacian_v1
import CoulombDomainTotal_v2

/-! Symmetry of the actual weak continuum Coulomb graph, including the full
fermionic spin-space realization. No self-adjointness claim is made here. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem real_multiplier_pairing_symmetric {N : ℕ} (V : Configuration N → ℝ)
    (f g vf vg : SpatialL2 N)
    (hf : vf =ᵐ[volume] fun x => (V x : ℂ) * f x)
    (hg : vg =ᵐ[volume] fun x => (V x : ℂ) * g x) :
    inner ℂ f vg = inner ℂ vf g := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf, hg] with x hx hx'
  rw [hx, hx']
  simp only [RCLike.inner_apply', map_mul, Complex.conj_ofReal]
  ring

theorem scalar_graph_value_decomposition {N : ℕ} {Z : ℝ} {f h v : SpatialL2 N}
    (e : Coordinate N → Coordinate N → SpatialL2 N)
    (hout : ∀ᵐ x : Configuration N, h x = (-((1 : ℂ)/2)) * (∑ k, e k k x) +
      (coulombPotential N Z x : ℂ) * f x)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    h = (-((1 : ℂ)/2)) • (∑ k : Coordinate N, e k k) + v := by
  apply Lp.ext
  filter_upwards [hout, hv,
    Lp.coeFn_add ((-((1 : ℂ)/2)) • (∑ k : Coordinate N, e k k)) v,
    Lp.coeFn_smul (-((1 : ℂ)/2)) (∑ k : Coordinate N, e k k),
    Lp.coeFn_fun_finsetSum Finset.univ (fun k => e k k)] with x hx hvx hax hsx hsumx
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hax hsx
  rw [hax, hsx, hsumx, hvx, hx]

/-- Symmetry on the actual scalar Coulomb graph. All potential-product existence
and weak Laplacian integration-by-parts obligations are proved dependencies. -/
theorem scalar_graph_symmetric {N : ℕ} {Z : ℝ} {f g hf hg : SpatialL2 N}
    (hfg : scalarHamiltonianGraph N Z f hf) (hgg : scalarHamiltonianGraph N Z g hg) :
    inner ℂ f hg = inner ℂ hf g := by
  have hvf := coulombProductL2_of_scalar_graph hfg
  have hvg := coulombProductL2_of_scalar_graph hgg
  let vf : SpatialL2 N := hvf.toLp (fun x => (coulombPotential N Z x : ℂ)*f x)
  let vg : SpatialL2 N := hvg.toLp (fun x => (coulombPotential N Z x : ℂ)*g x)
  have havf : vf =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ)*f x := hvf.coeFn_toLp
  have havg : vg =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ)*g x := hvg.coeFn_toLp
  obtain ⟨df, ef, hdf, hef, houtf⟩ := hfg
  obtain ⟨dg, eg, hdg, heg, houtg⟩ := hgg
  rw [scalar_graph_value_decomposition eg houtg havg,
    scalar_graph_value_decomposition ef houtf havf]
  rw [inner_add_right, inner_add_left, inner_smul_right, inner_smul_left]
  rw [weak_laplacian_symmetric df dg (fun k => ef k k) (fun k => eg k k)
    hdf hdg (fun k => hef k k) (fun k => heg k k),
    real_multiplier_pairing_symmetric _ f g vf vg havf havg]
  simp [starRingEnd_apply]

/-- Symmetry of the complete fermionic graph on the simultaneous-permutation
spin-space model. This is symmetry, with its exact weak H² domain proved elsewhere. -/
theorem hamiltonian_graph_symmetric {N : ℕ} {Z : ℝ} {f g hf hg : SpinSpace N}
    (hfg : hamiltonianGraph N Z f hf) (hgg : hamiltonianGraph N Z g hg) :
    inner ℂ f hg = inner ℂ hf g := by
  simp only [PiLp.inner_apply]
  exact Finset.sum_congr rfl (fun σ _ => scalar_graph_symmetric (hfg.2.2 σ) (hgg.2.2 σ))

#print axioms scalar_graph_symmetric
#print axioms hamiltonian_graph_symmetric
end TheoremT.Continuum
