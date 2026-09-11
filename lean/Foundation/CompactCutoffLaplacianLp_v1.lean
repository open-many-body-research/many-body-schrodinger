import CompactLocalMultiplierLp_v1
import LocalWeakLaplacian_v1

noncomputable section
open MeasureTheory Filter
open scoped ContDiff ENNReal
namespace TheoremT.Continuum

theorem realTestLaplacian_support_subset {N : ℕ} (χ : Configuration N → ℝ) :
    Function.support (realTestLaplacian χ) ⊆ tsupport χ := by
  intro x hx
  by_contra hn
  apply hx
  apply Finset.sum_eq_zero
  intro k hk
  apply image_eq_zero_of_notMem_tsupport (f := fun y => fderiv ℝ
    (fun z => fderiv ℝ χ z (coordinateVector k)) y (coordinateVector k))
  intro hm
  exact hn ((tsupport_fderiv_apply_subset ℝ (coordinateVector k))
    ((tsupport_fderiv_apply_subset ℝ (coordinateVector k)) hm))

theorem compact_cutoff_laplacian_rhs_memLp {N : ℕ} {q : ℝ≥0∞}
    {S : Set (Configuration N)} (hS : MeasurableSet S)
    {χ : Configuration N → ℝ} (hχ : ContDiff ℝ ∞ χ) (hc : HasCompactSupport χ)
    (hs : tsupport χ ⊆ S) {f L : Configuration N → ℂ} {d : Coordinate N → Configuration N → ℂ}
    (hf : MemLp f q (volume.restrict S)) (hL : MemLp L q (volume.restrict S))
    (hd : ∀ k, MemLp (d k) q (volume.restrict S)) :
    MemLp (fun x => (χ x : ℂ)*L x+2*(∑ k, (fderiv ℝ χ x (coordinateVector k) : ℂ)*d k x)+
      (realTestLaplacian χ x : ℂ)*f x) q volume := by
  have h₀ : MemLp (fun x => (χ x : ℂ)*L x) q volume := by
    simpa only [Complex.real_smul] using compact_multiplier_memLp_of_local hS
      (hχ.continuous.memLp_top_of_hasCompactSupport hc volume) ((subset_tsupport χ).trans hs) hL
  have hD (k : Coordinate N) : MemLp (fun x => (fderiv ℝ χ x (coordinateVector k) : ℂ)*d k x) q volume := by
    have hm : MemLp (fun x => fderiv ℝ χ x (coordinateVector k)) ⊤ volume :=
      ((hχ.continuous_fderiv (by simp)).clm_apply continuous_const).memLp_top_of_hasCompactSupport
        (hc.fderiv_apply ℝ (coordinateVector k)) volume
    have hsD : Function.support (fun x => fderiv ℝ χ x (coordinateVector k)) ⊆ S :=
      (subset_tsupport _).trans ((tsupport_fderiv_apply_subset ℝ (coordinateVector k)).trans hs)
    simpa only [Complex.real_smul] using compact_multiplier_memLp_of_local hS hm hsD (hd k)
  have h₂ : MemLp (fun x => (realTestLaplacian χ x : ℂ)*f x) q volume := by
    simpa only [Complex.real_smul] using compact_multiplier_memLp_of_local hS
      ((realTestLaplacian_continuous hχ).memLp_top_of_hasCompactSupport (realTestLaplacian_compact hc) volume)
      ((realTestLaplacian_support_subset χ).trans hs) hf
  have hsum := memLp_finsetSum Finset.univ (fun k hk => hD k)
  have hb : MemLp (fun x => 2*(∑ k, (fderiv ℝ χ x (coordinateVector k) : ℂ)*d k x)) q volume :=
    hsum.const_mul 2
  exact (h₀.add hb).add h₂

#print axioms compact_cutoff_laplacian_rhs_memLp
end TheoremT.Continuum
