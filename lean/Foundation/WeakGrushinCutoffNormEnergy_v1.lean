import WeakGrushinCutoffNormSupport_v1

/-! Actual restricted first-jet energy, with all terms integrable on a compact
set. This quantity is used in the quantitative cutoff commutator estimate. -/
noncomputable section
open MeasureTheory
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def firstJetEnergyOn (c : ℝ) (K : Set (Space κ))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) : ℝ :=
  (∑ i : Fin 4, ∫ p in K, ‖d (yDir i) p‖^2) +
    c * (∑ j : κ, ∫ p in K, ‖p.1‖^2 * ‖d (tDir j) p‖^2)

theorem firstJetEnergyOn_nonneg {c : ℝ} (hc : 0 ≤ c) (K : Set (Space κ))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    0 ≤ firstJetEnergyOn c K d := by
  apply add_nonneg
  · exact Finset.sum_nonneg (fun i _ => integral_nonneg (fun p => sq_nonneg _))
  · exact mul_nonneg hc (Finset.sum_nonneg (fun j _ =>
      integral_nonneg (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _))))

theorem compact_firstJetEnergyOn_integral (c : ℝ)
    {K : Set (Space κ)} (hK : IsCompact K)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    (∫ p in K, (∑ i : Fin 4, ‖d (yDir i) p‖^2) +
      c*‖p.1‖^2*(∑ j : κ, ‖d (tDir j) p‖^2)) = firstJetEnergyOn c K d := by
  have iy (i : Fin 4) : IntegrableOn (fun p => ‖d (yDir i) p‖^2) K volume :=
    ((Lp.memLp (d (yDir i))).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integrableOn
  have it (j : κ) : IntegrableOn (fun p => ‖p.1‖^2*‖d (tDir j) p‖^2) K volume :=
    compact_weighted_jet_integrable_norm_sq hK (fun p => ‖p.1‖^2)
      (by fun_prop) (d (tDir j))
  have iys : IntegrableOn (fun p => ∑ i : Fin 4, ‖d (yDir i) p‖^2) K volume :=
    integrable_finsetSum _ (fun i _ => iy i)
  have its : IntegrableOn (fun p => ∑ j : κ, ‖p.1‖^2*‖d (tDir j) p‖^2) K volume :=
    integrable_finsetSum _ (fun j _ => it j)
  have he (p : Space κ) : c*‖p.1‖^2*(∑ j : κ, ‖d (tDir j) p‖^2) =
      c*(∑ j : κ, ‖p.1‖^2*‖d (tDir j) p‖^2) := by
    rw [← Finset.mul_sum]
    ring
  simp_rw [he]
  rw [integral_add iys (its.const_mul c),integral_const_mul,
    integral_finsetSum _ (fun i _ => iy i),integral_finsetSum _ (fun j _ => it j)]
  rfl

#print axioms firstJetEnergyOn_nonneg
#print axioms compact_firstJetEnergyOn_integral
end TheoremT.Continuum.WeakGrushin
