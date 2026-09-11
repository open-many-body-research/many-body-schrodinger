import ContinuumFoundation_v1

/-!
Algebraic assembly of the actual weak Coulomb graph. This is an exact
characterization, not a proof of the still-needed Hardy multiplier premise.
No scalar or physical domain is silently enlarged or replaced.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum

/-- The remaining scalar multiplication obligation, using the actual potential. -/
def CoulombProductL2 {N : ℕ} (Z : ℝ) (f : SpatialL2 N) : Prop :=
  MemLp (fun x => (coulombPotential N Z x : ℂ) * f x) 2 volume

theorem diagonal_sum_memLp {N : ℕ}
    (e : Coordinate N → Coordinate N → SpatialL2 N) :
    MemLp (fun x => ∑ k, e k k x) 2 volume := by
  exact memLp_finsetSum Finset.univ (fun k _ => Lp.memLp (e k k))

/-- Given the actual multiplier fact, the H2 weak graph output exists. -/
theorem scalar_graph_exists_of_coulombProductL2 {N : ℕ} {Z : ℝ}
    {f : SpatialL2 N} (hf : HasH2 f) (hv : CoulombProductL2 Z f) :
    ∃ h : SpatialL2 N, scalarHamiltonianGraph N Z f h := by
  obtain ⟨d, hd, he⟩ := hf
  choose e he using he
  let kinetic : Configuration N → ℂ := fun x =>
    (-((1 : ℂ) / 2)) * (∑ k, e k k x)
  have hk : MemLp kinetic 2 volume := by
    exact (diagonal_sum_memLp e).const_mul _
  have hout : MemLp (fun x => kinetic x + (coulombPotential N Z x : ℂ) * f x)
      2 volume := hk.add hv
  refine ⟨hout.toLp _, d, e, hd, he, ?_⟩
  exact hout.coeFn_toLp

/-- A weak graph output forces the physical Coulomb product to be in L2. -/
theorem coulombProductL2_of_scalar_graph {N : ℕ} {Z : ℝ} {f h : SpatialL2 N}
    (hg : scalarHamiltonianGraph N Z f h) : CoulombProductL2 Z f := by
  obtain ⟨d, e, hd, he, hout⟩ := hg
  have hk := (diagonal_sum_memLp e).const_mul (-((1 : ℂ) / 2))
  apply MemLp.ae_eq (hf_Lp := (Lp.memLp h).sub hk)
  filter_upwards [hout] with x hx
  change h x - (-((1 : ℂ) / 2)) * (∑ k, e k k x) = _
  rw [hx]
  ring

/-- Exactly the H2 and multiplier conditions, with unique output. -/
theorem scalar_graph_existsUnique_iff {N : ℕ} {Z : ℝ} {f : SpatialL2 N} :
    (∃! h : SpatialL2 N, scalarHamiltonianGraph N Z f h) ↔
      HasH2 f ∧ CoulombProductL2 Z f := by
  constructor
  · rintro ⟨h, hg, _⟩
    exact ⟨scalar_graph_hasH2 hg, coulombProductL2_of_scalar_graph hg⟩
  · rintro ⟨hf, hv⟩
    obtain ⟨h, hg⟩ := scalar_graph_exists_of_coulombProductL2 hf hv
    exact ⟨h, hg, fun h' hh' => scalar_graph_unique hh' hg⟩

#print axioms diagonal_sum_memLp
#print axioms scalar_graph_exists_of_coulombProductL2
#print axioms coulombProductL2_of_scalar_graph
#print axioms scalar_graph_existsUnique_iff
end TheoremT.Continuum
