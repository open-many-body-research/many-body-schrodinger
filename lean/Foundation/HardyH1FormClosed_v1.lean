import HardyH1FormBounds_v1
import CoulombH1Continuity_v1

/-! Completeness in the actual shifted Coulomb form energy. The Cauchy
condition is stated explicitly in squared form differences, avoiding any
unproved replacement norm. The resulting limit is in the genuine H¹ domain
and convergence holds for the value and every first weak derivative. -/
noncomputable section
set_option maxHeartbeats 1600000
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum

theorem fermionicH1Graph_eval_continuous (N : ℕ) (i : Option (Coordinate N)) :
    Continuous (fun a : fermionicH1Graph N => a.val i) :=
  (PiLp.continuous_apply 2 _ i).comp continuous_subtype_val

theorem fermionicH1FormEnergy_continuous (N : ℕ) (Z : ℝ) :
    Continuous (fermionicH1FormEnergy (N := N) Z) := by
  have hex (a : fermionicH1Graph N) := spin_coulomb_product_exists_of_hasH1 Z (a.val none)
    (fun σ => ⟨fun k => a.val (some k) σ, a.property.2 σ⟩)
  choose v hv using hex
  have he (a : fermionicH1Graph N) : fermionicH1FormEnergy Z a =
      coulombH1Energy (a.val none) (fun k => a.val (some k)) (v a) := by
    apply coulombH1FormValue_unique (fermionicH1FormEnergy_spec Z a)
    exact ⟨a.property.1, fun k => a.val (some k), v a, a.property.2, hv a, rfl⟩
  apply continuous_iff_seqContinuous.mpr
  intro a a₀ ha
  have ht (i : Option (Coordinate N)) :
      Tendsto (fun n => (a n).val i) atTop (nhds (a₀.val i)) :=
    ((fermionicH1Graph_eval_continuous N i).tendsto a₀).comp ha
  change Tendsto (fun n => fermionicH1FormEnergy Z (a n)) atTop
    (nhds (fermionicH1FormEnergy Z a₀))
  simp_rw [he]
  exact coulombH1Energy_tendsto Z (fun n => (a n).val none) (a₀.val none)
    (fun n k => (a n).val (some k)) (fun k => a₀.val (some k))
    (fun n => v (a n)) (v a₀) (fun n => (a n).property.2) a₀.property.2
    (fun n => hv (a n)) (hv a₀) (ht none) (fun k => ht (some k))

theorem fermionicH1Form_shift_difference_tendsto {N : ℕ} (Z : ℝ)
    {a : ℕ → fermionicH1Graph N} {a₀ : fermionicH1Graph N}
    (ha : Tendsto a atTop (nhds a₀)) :
    Tendsto (fun n => fermionicH1FormEnergy Z (a n - a₀) +
      h1FormShift N Z * ‖(a n - a₀).val none‖^2) atTop (nhds 0) := by
  have ht : Tendsto (fun n => h1FormNormUpper N Z * ‖a n - a₀‖^2)
      atTop (nhds 0) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero]
      using (((ha.sub_const a₀).norm.pow 2).const_mul (h1FormNormUpper N Z))
  apply squeeze_zero (fun n => ?_) (fun n => (fermionicH1FormEnergy_shift_bounds Z (a n - a₀)).2) ht
  exact le_trans (by positivity) (fermionicH1FormEnergy_shift_bounds Z (a n - a₀)).1

/-- Every Cauchy sequence in the squared shifted physical form energy has an
actual weak-H¹ fermionic limit and converges in that same shifted energy.
Its value and all first weak derivatives converge in L² by the graph topology. -/
theorem fermionicH1Form_cauchy_complete {N : ℕ} (Z : ℝ)
    (a : ℕ → fermionicH1Graph N)
    (hc : ∀ ε > (0 : ℝ), ∃ n₀ : ℕ, ∀ m ≥ n₀, ∀ n ≥ n₀,
      fermionicH1FormEnergy Z (a m - a n) +
        h1FormShift N Z * ‖(a m - a n).val none‖^2 < ε) :
    ∃ a₀ : fermionicH1Graph N,
      Tendsto a atTop (nhds a₀) ∧
      Tendsto (fun n => fermionicH1FormEnergy Z (a n - a₀) +
        h1FormShift N Z * ‖(a n - a₀).val none‖^2) atTop (nhds 0) ∧
      Tendsto (fun n => fermionicH1FormEnergy Z (a n))
        atTop (nhds (fermionicH1FormEnergy Z a₀)) := by
  have hca : CauchySeq a := by
    apply Metric.cauchySeq_iff.mpr
    intro ε hε
    obtain ⟨n₀, hn₀⟩ := hc (ε^2 / 4) (by positivity)
    refine ⟨n₀, ?_⟩
    intro m hm n hn
    have hsmall := hn₀ m hm n hn
    have hb := (fermionicH1FormEnergy_shift_bounds Z (a m - a n)).1
    rw [dist_eq_norm]
    nlinarith [norm_nonneg (a m - a n)]
  obtain ⟨a₀, ha₀⟩ := cauchySeq_tendsto_of_complete hca
  exact ⟨a₀, ha₀, fermionicH1Form_shift_difference_tendsto Z ha₀,
    ((fermionicH1FormEnergy_continuous N Z).tendsto a₀).comp ha₀⟩

#print axioms fermionicH1FormEnergy_continuous
#print axioms fermionicH1Form_shift_difference_tendsto
#print axioms fermionicH1Form_cauchy_complete
end TheoremT.Continuum
