import WeakGrushinCutoffPrincipalMemLp_v1
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Genuine support and integrability facts for quantitative weak Grushin
cutoff estimates. No numerical upper bound is assumed in these facts. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def combinedCutoffError (c : ℝ) (χ : Space κ → ℝ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (p : Space κ) : ℂ :=
  cutoffYError χ f d p + (c*‖p.1‖^2) • cutoffTError χ f d p

theorem combinedCutoffError_memLp (c : ℝ)
    {χ : Space κ → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) :
    MemLp (combinedCutoffError c χ f d) 2 volume := by
  change MemLp (fun p => cutoffYError χ f d p +
    (c*‖p.1‖^2) • cutoffTError χ f d p) 2 volume
  exact (cutoffYError_memLp hχ hcχ f d).add (weighted_cutoffTError_memLp c hχ hcχ f d)

theorem combinedCutoffError_eq_zero_of_notMem_tsupport
    (c : ℝ) (χ : Space κ → ℝ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)))
    {p : Space κ} (hp : p ∉ tsupport χ) : combinedCutoffError c χ f d p = 0 := by
  have hD (v : Space κ) : fderiv ℝ χ p v = 0 := by
    rw [fderiv_of_notMem_tsupport ℝ hp]
    rfl
  have hDD (v w : Space κ) : fderiv ℝ (fun q => fderiv ℝ χ q v) p w = 0 := by
    have hz : p ∉ tsupport (fun q => fderiv ℝ χ q v) :=
      fun hh => hp ((tsupport_fderiv_apply_subset ℝ v) hh)
    rw [fderiv_of_notMem_tsupport ℝ hz]
    rfl
  simp only [combinedCutoffError,cutoffYError,cutoffTError,hD,hDD,
    zero_smul,mul_zero,add_zero,Finset.sum_const_zero,smul_zero]

theorem combinedCutoffError_integral_norm_sq_eq_setIntegral
    (c : ℝ) (χ : Space κ → ℝ)
    (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)))
    {K : Set (Space κ)} (hK : tsupport χ ⊆ K) :
    (∫ p, ‖combinedCutoffError c χ f d p‖^2) =
      ∫ p in K, ‖combinedCutoffError c χ f d p‖^2 := by
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro p hp
  rw [combinedCutoffError_eq_zero_of_notMem_tsupport c χ f d (fun hh => hp (hK hh))]
  norm_num

theorem compact_weighted_jet_integrable_norm_sq
    {K : Set (Space κ)} (hK : IsCompact K) (a : Space κ → ℝ)
    (ha : Continuous a) (f : Lp ℂ 2 (volume : Measure (Space κ))) :
    IntegrableOn (fun p => a p * ‖f p‖^2) K volume := by
  have hf : IntegrableOn (fun p => ‖f p‖^2) K volume :=
    ((Lp.memLp f).integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)).integrableOn
  exact hf.continuousOn_mul ha.continuousOn hK

#print axioms combinedCutoffError_memLp
#print axioms combinedCutoffError_eq_zero_of_notMem_tsupport
#print axioms combinedCutoffError_integral_norm_sq_eq_setIntegral
#print axioms compact_weighted_jet_integrable_norm_sq
end TheoremT.Continuum.WeakGrushin
