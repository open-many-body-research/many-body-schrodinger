import WeakGrushinCutoffNormPointwise_v1
import WeakGrushinCutoffNormEnergy_v1

/-! Quantitative integral bound for the actual combined weak Grushin cutoff
error. The first-jet energy is restricted to a compact set containing the
cutoff support. All integrability is proved from actual L² inputs. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_firstJetEnergyDensity_integrable (c : ℝ)
    {K : Set (Space κ)} (hK : IsCompact K)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    IntegrableOn (firstJetEnergyDensity c d) K volume := by
  have iy (i : Fin 4) : IntegrableOn (fun p => ‖d (yDir i) p‖^2) K volume :=
    ((Lp.memLp (d (yDir i))).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integrableOn
  have it (j : κ) : IntegrableOn (fun p => (c*‖p.1‖^2)*‖d (tDir j) p‖^2) K volume :=
    compact_weighted_jet_integrable_norm_sq hK (fun p => c*‖p.1‖^2)
      (by fun_prop) (d (tDir j))
  have iys := integrable_finsetSum Finset.univ (fun i _ => iy i)
  have its := integrable_finsetSum Finset.univ (fun j _ => it j)
  change Integrable (fun p => (∑ i : Fin 4, ‖d (yDir i) p‖^2) +
    (c*‖p.1‖^2)*(∑ j : κ, ‖d (tDir j) p‖^2)) (volume.restrict K)
  simpa only [Finset.mul_sum,Pi.add_def] using iys.add its

theorem compact_firstJetEnergyDensity_integral (c : ℝ)
    {K : Set (Space κ)} (hK : IsCompact K)
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    (∫ p in K, firstJetEnergyDensity c d p) = firstJetEnergyOn c K d :=
  compact_firstJetEnergyOn_integral c hK d

theorem combinedCutoffError_integral_norm_sq_le {c : ℝ} (hc : 0 ≤ c)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)))
    {K : Set (Space κ)} (hK : IsCompact K) (hs : tsupport χ ⊆ K)
    (A B : ℝ)
    (hA : ∀ p ∈ K, |combinedCutoffScalar c χ p| ≤ A)
    (hB : ∀ p ∈ K, cutoffGradientWeight c χ p ≤ B) :
    (∫ p, ‖combinedCutoffError c χ f d p‖^2) ≤
      2*A^2*(∫ p in K, ‖f p‖^2) + 8*B*firstJetEnergyOn c K d := by
  have ifn : IntegrableOn (fun p => ‖f p‖^2) K volume :=
    ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integrableOn
  have ien := compact_firstJetEnergyDensity_integrable c hK d
  have icn : IntegrableOn (fun p => ‖combinedCutoffError c χ f d p‖^2) K volume :=
    ((combinedCutoffError_memLp c hχ hcχ f d).integrable_norm_pow
      (by norm_num : (2 : ℕ) ≠ 0)).integrableOn
  have ir : IntegrableOn (fun p => 2*A^2*‖f p‖^2 +
      8*B*firstJetEnergyDensity c d p) K volume :=
    (ifn.const_mul (2*A^2)).add (ien.const_mul (8*B))
  rw [combinedCutoffError_integral_norm_sq_eq_setIntegral c χ f d hs]
  calc
    _ ≤ ∫ p in K, 2*A^2*‖f p‖^2 + 8*B*firstJetEnergyDensity c d p := by
      apply integral_mono_ae icn ir
      filter_upwards [ae_restrict_mem hK.measurableSet] with p hp
      have hpoint := cutoff_error_norm_sq_le hc χ f d p
      have ha2 : |combinedCutoffScalar c χ p|^2 ≤ A^2 :=
        pow_le_pow_left₀ (abs_nonneg _) (hA p hp) 2
      have ha := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left ha2 (by norm_num : (0 : ℝ) ≤ 2)) (sq_nonneg ‖f p‖)
      have hb := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (hB p hp) (by norm_num : (0 : ℝ) ≤ 8))
        (firstJetEnergyDensity_nonneg hc d p)
      exact hpoint.trans (add_le_add ha hb)
    _ = _ := by
      rw [integral_add (ifn.const_mul (2*A^2)) (ien.const_mul (8*B)),
        integral_const_mul,integral_const_mul,compact_firstJetEnergyDensity_integral c hK d]

#print axioms compact_firstJetEnergyDensity_integrable
#print axioms compact_firstJetEnergyDensity_integral
#print axioms combinedCutoffError_integral_norm_sq_le
end TheoremT.Continuum.WeakGrushin
