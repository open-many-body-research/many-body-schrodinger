import HardyCoulombSymmetry_v1

/-! Pair the actual H² Coulomb graph against arbitrary actual weak H¹ tests.
This supplies weighted eigenfunction identities without assuming extra operator
powers or compact support of the eigenfunction. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum

theorem scalar_graph_h1_pairing_complex {N : ℕ} {Z : ℝ} {f h v a : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f h) (df da : Coordinate N → SpatialL2 N)
    (hdf : ∀ k, WeakPartial f (df k) k) (hda : ∀ k, WeakPartial a (da k) k)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    inner ℂ a h = (1/2 : ℂ) * (∑ k, inner ℂ (da k) (df k)) + inner ℂ a v := by
  obtain ⟨df',e,hd',he,hout⟩ := hg
  have heq : df' = df := funext (fun k => weakPartial_unique (hd' k) (hdf k))
  subst df'
  rw [scalar_graph_value_decomposition e hout hv,inner_add_right,inner_smul_right,inner_sum]
  simp_rw [fun k => weakPartial_complex_ibp (hda k) (he k k)]
  rw [Finset.sum_neg_distrib]
  ring

theorem scalar_graph_h1_pairing_real {N : ℕ} {Z : ℝ} {f h v a : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f h) (df da : Coordinate N → SpatialL2 N)
    (hdf : ∀ k, WeakPartial f (df k) k) (hda : ∀ k, WeakPartial a (da k) k)
    (hv : v =ᵐ[volume] fun x => (coulombPotential N Z x : ℂ) * f x) :
    inner ℝ a h = (1/2 : ℝ) * (∑ k, inner ℝ (da k) (df k)) + inner ℝ a v := by
  have ht := congrArg Complex.re (scalar_graph_h1_pairing_complex hg df da hdf hda hv)
  simp only [Complex.add_re,Complex.mul_re] at ht
  simp only [spatialL2_real_inner_eq_re]
  convert ht using 1 <;> norm_num

#print axioms scalar_graph_h1_pairing_complex
#print axioms scalar_graph_h1_pairing_real
end TheoremT.Continuum
