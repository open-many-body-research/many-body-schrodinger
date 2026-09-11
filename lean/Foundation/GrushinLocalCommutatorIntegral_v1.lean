import GrushinCommutatorIntegral_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum

theorem nuclear_KS_continuous_commutator_integral_tendsto_zero {N : ℕ} (i : Fin N)
    {φ : NuclearKSSpace i → ℝ} (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ)
    {u : NuclearKSSpace i → ℂ} (hu : Continuous u)
    {δ : ℕ → ℝ} (hδ : ∀ n, 0 < δ n) (hδ1 : ∀ n, δ n ≤ 1)
    (hd : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => ∫ q, (ksHoleCommutator (δ n) φ q : ℂ)*u q) atTop (𝓝 0) := by
  classical
  obtain ⟨M,hM⟩ := hc.isCompact.exists_bound_of_continuousOn hu.continuousOn
  let u' : NuclearKSSpace i → ℂ := (tsupport φ).indicator u
  have hb (q : NuclearKSSpace i) : ‖u' q‖ ≤ max M 0 := by
    by_cases hq : q ∈ tsupport φ
    · simpa [u',hq] using (hM q hq).trans (le_max_left M 0)
    · simp only [u',Set.indicator_of_notMem hq,norm_zero]
      exact le_max_right M 0
  have he (n : ℕ) : (fun q => (ksHoleCommutator (δ n) φ q : ℂ)*u' q) =
      (fun q => (ksHoleCommutator (δ n) φ q : ℂ)*u q) := by
    funext q
    by_cases hq : q ∈ tsupport φ
    · simp [u',hq]
    · simp [u',hq,ksHoleCommutator_zero_off_test hq]
  have hh := nuclear_KS_commutator_integral_tendsto_zero i hφ hc hb hδ hδ1 hd
  simpa only [he] using hh

#print axioms nuclear_KS_continuous_commutator_integral_tendsto_zero
end TheoremT.Continuum
