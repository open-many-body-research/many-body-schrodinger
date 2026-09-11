import CompactCoulombL2_v2
import HardyWeakTransfer_v3

/-! Actual weak-H¹ Coulomb multiplication for every finite electron count.
The first transfer uses the full gradient and therefore does not assert the
sharper directional constants of the compact-core inequalities. -/

noncomputable section
open MeasureTheory
open scoped BigOperators ContDiff

namespace TheoremT.Continuum

theorem electronGradientEnergy_le_full {N : ℕ} (i : Fin N)
    (u : Configuration N → ℂ) (x : Configuration N) :
    electronGradientEnergy i u x ≤
      ∑ k : Coordinate N, ‖fderiv ℝ u x (coordinateVector k)‖^2 := by
  rw [Fintype.sum_prod_type]
  exact Finset.single_le_sum (f := fun j : Fin N =>
    ∑ k : Fin 3, ‖fderiv ℝ u x (coordinateVector (j, k))‖^2)
    (fun j _ => Finset.sum_nonneg (fun k _ => sq_nonneg _))
    (Finset.mem_univ i)

theorem fullGradientEnergy_integrable {N : ℕ} {u : Configuration N → ℂ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Integrable (fun x => ∑ k : Coordinate N, ‖fderiv ℝ u x (coordinateVector k)‖^2) volume := by
  simpa only [Fintype.sum_prod_type, electronGradientEnergy] using
    (integrable_finsetSum (s := Finset.univ)
      (fun i _ => electronGradientEnergy_integrable i hu huc))

theorem electronGradientEnergy_integral_le_full {N : ℕ} (i : Fin N)
    {u : Configuration N → ℂ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    (∫ x, electronGradientEnergy i u x) ≤
      ∫ x, ∑ k : Coordinate N, ‖fderiv ℝ u x (coordinateVector k)‖^2 :=
  integral_mono (electronGradientEnergy_integrable i hu huc)
    (fullGradientEnergy_integrable hu huc) (electronGradientEnergy_le_full i u)

theorem weak_nuclear_hardy_integrable_sq_and_bound {N : ℕ} (i : Fin N)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x => ‖f x‖^2 / ‖position x i‖^2) volume ∧
      (∫ x, ‖f x‖^2 / ‖position x i‖^2) ≤
        4 * (∑ k : Coordinate N, ‖d k‖^2) := by
  have hcore : ∀ u : Configuration N → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      Integrable (fun x => (‖position x i‖^2)⁻¹ * ‖u x‖^2) volume ∧
      (∫ x, (‖position x i‖^2)⁻¹ * ‖u x‖^2) ≤
        4 * (∫ x, ∑ k : Coordinate N, ‖fderiv ℝ u x (coordinateVector k)‖^2) := by
    intro u hu huc
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by simp)
    have h := compact_nuclear_hardy_integrable_sq_and_bound i hu1 huc
    constructor
    · simpa only [div_eq_mul_inv, mul_comm] using h.1
    · have hh := h.2.trans (mul_le_mul_of_nonneg_left
        (electronGradientEnergy_integral_le_full i hu1 huc) (by norm_num : (0 : ℝ) ≤ 4))
      simpa only [div_eq_mul_inv, mul_comm] using hh
  have h := compact_core_bound_extends_weakH1 (fun x => (‖position x i‖^2)⁻¹)
    (fun x => inv_nonneg.mpr (sq_nonneg _)) (by norm_num : (0 : ℝ) ≤ 4) hcore f d hd
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem weak_pair_hardy_integrable_sq_and_bound {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    Integrable (fun x => ‖f x‖^2 / ‖position x i - position x j‖^2) volume ∧
      (∫ x, ‖f x‖^2 / ‖position x i - position x j‖^2) ≤
        4 * (∑ k : Coordinate N, ‖d k‖^2) := by
  have hcore : ∀ u : Configuration N → ℂ, ContDiff ℝ ∞ u → HasCompactSupport u →
      Integrable (fun x => (‖position x i - position x j‖^2)⁻¹ * ‖u x‖^2) volume ∧
      (∫ x, (‖position x i - position x j‖^2)⁻¹ * ‖u x‖^2) ≤
        4 * (∫ x, ∑ k : Coordinate N, ‖fderiv ℝ u x (coordinateVector k)‖^2) := by
    intro u hu huc
    have hu1 : ContDiff ℝ 1 u := hu.of_le (by simp)
    have h := compact_pair_hardy_integrable_sq_and_bound i j hij hu1 huc
    constructor
    · simpa only [div_eq_mul_inv, mul_comm] using h.1
    · have hh := h.2.trans (mul_le_mul_of_nonneg_left
        (electronGradientEnergy_integral_le_full i hu1 huc) (by norm_num : (0 : ℝ) ≤ 4))
      simpa only [div_eq_mul_inv, mul_comm] using hh
  have h := compact_core_bound_extends_weakH1
    (fun x => (‖position x i - position x j‖^2)⁻¹)
    (fun x => inv_nonneg.mpr (sq_nonneg _)) (by norm_num : (0 : ℝ) ≤ 4) hcore f d hd
  simpa only [div_eq_mul_inv, mul_comm] using h

theorem weak_nuclear_memLp_two_and_bound {N : ℕ} (i : Fin N)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    MemLp (fun x => f x / (‖position x i‖ : ℂ)) 2 volume ∧
      (∫ x, ‖f x / (‖position x i‖ : ℂ)‖^2) ≤ 4 * (∑ k : Coordinate N, ‖d k‖^2) := by
  have h := weak_nuclear_hardy_integrable_sq_and_bound i f d hd
  have hm : AEStronglyMeasurable (fun x => f x / (‖position x i‖ : ℂ)) volume :=
    ((Lp.memLp f).aestronglyMeasurable.aemeasurable.div
      (Complex.ofRealCLM.continuous.comp
        (continuous_position i).norm).measurable.aemeasurable).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.1
  · simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.2

theorem weak_pair_memLp_two_and_bound {N : ℕ} (i j : Fin N) (hij : i ≠ j)
    (f : SpatialL2 N) (d : Coordinate N → SpatialL2 N)
    (hd : ∀ k, WeakPartial f (d k) k) :
    MemLp (fun x => f x / (‖position x i - position x j‖ : ℂ)) 2 volume ∧
      (∫ x, ‖f x / (‖position x i - position x j‖ : ℂ)‖^2) ≤
        4 * (∑ k : Coordinate N, ‖d k‖^2) := by
  have h := weak_pair_hardy_integrable_sq_and_bound i j hij f d hd
  have hm : AEStronglyMeasurable
      (fun x => f x / (‖position x i - position x j‖ : ℂ)) volume :=
    ((Lp.memLp f).aestronglyMeasurable.aemeasurable.div
      (Complex.ofRealCLM.continuous.comp
        ((continuous_position i).sub
          (continuous_position j)).norm).measurable.aemeasurable).aestronglyMeasurable
  constructor
  · apply (memLp_two_iff_integrable_sq_norm hm).2
    simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.1
  · simpa only [norm_div, Complex.norm_real, norm_norm, div_pow] using h.2

theorem coulombProductL2_of_hasH1 {N : ℕ} (Z : ℝ) {f : SpatialL2 N}
    (hf : HasH1 f) : CoulombProductL2 Z f := by
  obtain ⟨d, hd⟩ := hf
  have hn : MemLp (fun x => ∑ i : Fin N, f x / (‖position x i‖ : ℂ)) 2 volume :=
    memLp_finsetSum Finset.univ (fun i _ => (weak_nuclear_memLp_two_and_bound i f d hd).1)
  have hp : MemLp (fun x => ∑ i : Fin N,
      ∑ j ∈ Finset.univ.filter (fun j : Fin N => i < j),
        f x / (‖position x i - position x j‖ : ℂ)) 2 volume := by
    apply memLp_finsetSum Finset.univ
    intro i _
    apply memLp_finsetSum _
    intro j hj
    exact (weak_pair_memLp_two_and_bound i j
      (ne_of_lt (Finset.mem_filter.mp hj).2) f d hd).1
  have h := (hn.const_mul (-Z : ℂ)).add hp
  apply h.ae_eq
  exact .of_forall (fun x => (coulomb_product_eq_sums Z f x).symm)

theorem coulombProductL2_of_hasH2 {N : ℕ} (Z : ℝ) {f : SpatialL2 N}
    (hf : HasH2 f) : CoulombProductL2 Z f :=
  coulombProductL2_of_hasH1 Z (h2_implies_h1 hf)

/-- Exact actual weak-H² scalar-domain existence, with no multiplier premise. -/
theorem scalar_graph_existsUnique_iff_hasH2 {N : ℕ} {Z : ℝ} {f : SpatialL2 N} :
    (∃! h : SpatialL2 N, scalarHamiltonianGraph N Z f h) ↔ HasH2 f := by
  rw [scalar_graph_existsUnique_iff]
  exact ⟨And.left, fun hf => ⟨hf, coulombProductL2_of_hasH2 Z hf⟩⟩

#print axioms electronGradientEnergy_le_full
#print axioms fullGradientEnergy_integrable
#print axioms electronGradientEnergy_integral_le_full
#print axioms weak_nuclear_hardy_integrable_sq_and_bound
#print axioms weak_pair_hardy_integrable_sq_and_bound
#print axioms weak_nuclear_memLp_two_and_bound
#print axioms weak_pair_memLp_two_and_bound
#print axioms coulombProductL2_of_hasH1
#print axioms coulombProductL2_of_hasH2
#print axioms scalar_graph_existsUnique_iff_hasH2

end TheoremT.Continuum
