import PairHardySlicing_v2
import GraphAssembly_v2
import HardyWeakCore_v1

/-! Actual physical Coulomb multiplication on compact C¹ representatives.
All finite sums use the original point-nucleus potential, with positive pair
repulsion. This is a compact-core result, not yet the arbitrary weak H¹ bound. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace TheoremT.Continuum

theorem compact_nuclear_memLp_two_and_bound {N : ℕ} (i : Fin N)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    MemLp (fun x => u x / (‖position x i‖ : ℂ)) 2 volume ∧
      (∫ x, ‖u x / (‖position x i‖ : ℂ)‖^2) ≤
        4 * (∫ x, electronGradientEnergy i u x) := by
  have h := compact_nuclear_hardy_integrable_sq_and_bound i hu huc
  have hm : AEStronglyMeasurable (fun x => u x / (‖position x i‖ : ℂ)) volume :=
    (hu.continuous.measurable.div
      (Complex.ofRealCLM.continuous.comp (continuous_position i).norm).measurable).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.1
  · simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.2

theorem compact_pair_memLp_two_and_bound {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    MemLp (fun x => u x / (‖position x i - position x j‖ : ℂ)) 2 volume ∧
      (∫ x, ‖u x / (‖position x i - position x j‖ : ℂ)‖^2) ≤
        4 * (∫ x, electronGradientEnergy i u x) := by
  have h := compact_pair_hardy_integrable_sq_and_bound i j hij hu huc
  have hm : AEStronglyMeasurable
      (fun x => u x / (‖position x i - position x j‖ : ℂ)) volume :=
    (hu.continuous.measurable.div
      (Complex.ofRealCLM.continuous.comp
        ((continuous_position i).sub (continuous_position j)).norm).measurable).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.1
  · simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.2

theorem coulomb_product_eq_sums {N : ℕ} (Z : ℝ) (u : Configuration N → ℂ)
    (x : Configuration N) :
    (coulombPotential N Z x : ℂ) * u x =
      (-Z : ℂ) * (∑ i : Fin N, u x / (‖position x i‖ : ℂ)) +
      ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
        u x / (‖position x i - position x j‖ : ℂ) := by
  simp [coulombPotential, Finset.mul_sum,
    div_eq_mul_inv, mul_add, mul_comm, mul_left_comm]

theorem compact_coulomb_memLp {N : ℕ} (Z : ℝ) {u : Configuration N → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    MemLp (fun x => (coulombPotential N Z x : ℂ) * u x) 2 volume := by
  have hn : MemLp (fun x => ∑ i : Fin N, u x / (‖position x i‖ : ℂ)) 2 volume :=
    memLp_finsetSum Finset.univ (fun i _ => (compact_nuclear_memLp_two_and_bound i hu huc).1)
  have hp : MemLp (fun x => ∑ i : Fin N,
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
        u x / (‖position x i - position x j‖ : ℂ)) 2 volume := by
    apply memLp_finsetSum Finset.univ
    intro i _
    apply memLp_finsetSum _
    intro j hj
    exact (compact_pair_memLp_two_and_bound i j
      (ne_of_lt (Finset.mem_filter.mp hj).2) hu huc).1
  have h := (hn.const_mul (-Z : ℂ)).add hp
  apply h.ae_eq
  exact .of_forall (fun x => (coulomb_product_eq_sums Z u x).symm)

theorem compact_coulombProductL2 {N : ℕ} (Z : ℝ) {u : Configuration N → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (hf : MemLp u 2 volume) :
    CoulombProductL2 Z (hf.toLp u) := by
  apply (compact_coulomb_memLp Z hu huc).ae_eq
  filter_upwards [hf.coeFn_toLp] with x hx
  exact congrArg (fun z : ℂ => (coulombPotential N Z x : ℂ) * z) hx.symm

/-- Every actual compact C² representative has a unique scalar weak Coulomb
Hamiltonian output, with the original weak-H² graph and physical potential. -/
theorem compact_scalar_graph_existsUnique {N : ℕ} (Z : ℝ) {u : Configuration N → ℂ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (hf : MemLp u 2 volume) :
    ∃! h : SpatialL2 N, scalarHamiltonianGraph N Z (hf.toLp u) h := by
  apply scalar_graph_existsUnique_iff.mpr
  exact ⟨compact_c2_hasH2 hu huc hf,
    compact_coulombProductL2 Z (hu.of_le (by norm_num)) huc hf⟩

#print axioms compact_nuclear_memLp_two_and_bound
#print axioms compact_pair_memLp_two_and_bound
#print axioms coulomb_product_eq_sums
#print axioms compact_coulomb_memLp
#print axioms compact_coulombProductL2
#print axioms compact_scalar_graph_existsUnique

end TheoremT.Continuum
