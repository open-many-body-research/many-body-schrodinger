import CompactSupportWeightedL2_v1

/-! Actual finite continuous-weighted sums preserve L2 convergence on one
common compact support, including convergence of their squared integral norms. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum
variable {E I : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Fintype I]

theorem compact_finite_weighted_L2_ae {K : Set E} (hK : IsCompact K)
    (χ : I → E → ℝ) (hχ : ∀ i, Continuous (χ i)) (f : I → Lp ℂ 2 μ)
    (hs : ∀ i, ∀ᵐ x ∂μ, x ∉ K → f i x = 0) :
    ((∑ i, compactSupportWeightedL2 hK (χ i) (hχ i) (f i)) : Lp ℂ 2 μ) =ᵐ[μ]
      (fun x => ∑ i, χ i x • f i x) := by
  have ha : ∀ᵐ x ∂μ, ∀ i, compactSupportWeightedL2 hK (χ i) (hχ i) (f i) x =
      χ i x • f i x := by
    rw [ae_all_iff]
    exact fun i => compactSupportWeightedL2_ae hK (χ i) (hχ i) (f i) (hs i)
  filter_upwards [ha,Lp.coeFn_fun_finsetSum Finset.univ
    (fun i => compactSupportWeightedL2 hK (χ i) (hχ i) (f i))] with x hx hsum
  simpa only [hx] using hsum

theorem compact_finite_weighted_memLp {K : Set E} (hK : IsCompact K)
    (χ : I → E → ℝ) (hχ : ∀ i, Continuous (χ i)) (f : I → Lp ℂ 2 μ)
    (hs : ∀ i, ∀ᵐ x ∂μ, x ∉ K → f i x = 0) :
    MemLp (fun x => ∑ i, χ i x • f i x) 2 μ :=
  (Lp.memLp (∑ i, compactSupportWeightedL2 hK (χ i) (hχ i) (f i))).ae_eq
    (compact_finite_weighted_L2_ae hK χ hχ f hs)

theorem compact_finite_weighted_norm_sq_tendsto {K : Set E} (hK : IsCompact K)
    (χ : I → E → ℝ) (hχ : ∀ i, Continuous (χ i))
    {g : ℕ → I → Lp ℂ 2 μ} {f : I → Lp ℂ 2 μ}
    (hg : ∀ i, Tendsto (fun n => g n i) atTop (𝓝 (f i)))
    (hs : ∀ n i, ∀ᵐ x ∂μ, x ∉ K → g n i x = 0) :
    Tendsto (fun n => ∫ x, ‖∑ i, χ i x • g n i x‖^2 ∂μ) atTop
      (𝓝 (∫ x, ‖∑ i, χ i x • f i x‖^2 ∂μ)) := by
  have hf (i : I) := lp_ae_zero_on_of_tendsto hK.measurableSet.compl (hg i) (fun n => hs n i)
  have he (q : I → Lp ℂ 2 μ) (hq : ∀ i, ∀ᵐ x ∂μ, x ∉ K → q i x = 0) :
      ‖∑ i, compactSupportWeightedL2 hK (χ i) (hχ i) (q i)‖^2 =
        ∫ x, ‖∑ i, χ i x • q i x‖^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [compact_finite_weighted_L2_ae hK χ hχ q hq] with x hx
    rw [hx,real_inner_self_eq_norm_sq]
  have ht : Tendsto (fun n => ∑ i, compactSupportWeightedL2 hK (χ i) (hχ i) (g n i)) atTop
      (𝓝 (∑ i, compactSupportWeightedL2 hK (χ i) (hχ i) (f i))) :=
    tendsto_finset_sum _ (fun i _ => compactSupportWeightedL2_tendsto hK (χ i) (hχ i) (hg i))
  have hh := ht.norm.pow 2
  simpa only [he _ hf,he _ (hs _)] using hh

end TheoremT.Continuum
