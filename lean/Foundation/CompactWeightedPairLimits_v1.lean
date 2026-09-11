import CompactFiniteWeightedL2_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators RealInnerProductSpace
namespace TheoremT.Continuum
variable {E I : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  {μ : Measure E} [Fintype I]

theorem compact_two_weighted_norm_sq_tendsto {K : Set E} (hK : IsCompact K)
    (χ ψ : E → ℝ) (hχ : Continuous χ) (hψ : Continuous ψ)
    {g h : ℕ → Lp ℂ 2 μ} {f k : Lp ℂ 2 μ}
    (hg : Tendsto g atTop (𝓝 f)) (hh : Tendsto h atTop (𝓝 k))
    (hsg : ∀ n, ∀ᵐ x ∂μ, x ∉ K → g n x = 0)
    (hsh : ∀ n, ∀ᵐ x ∂μ, x ∉ K → h n x = 0) :
    Tendsto (fun n => ∫ x, ‖χ x • g n x + ψ x • h n x‖^2 ∂μ) atTop
      (𝓝 (∫ x, ‖χ x • f x + ψ x • k x‖^2 ∂μ)) := by
  let a : Fin 2 → E → ℝ := fun i => if i = 0 then χ else ψ
  let q : ℕ → Fin 2 → Lp ℂ 2 μ := fun n i => if i = 0 then g n else h n
  let r : Fin 2 → Lp ℂ 2 μ := fun i => if i = 0 then f else k
  have ha (i : Fin 2) : Continuous (a i) := by
    dsimp [a]
    split_ifs <;> assumption
  have hq (i : Fin 2) : Tendsto (fun n => q n i) atTop (𝓝 (r i)) := by
    dsimp [q,r]
    split_ifs <;> assumption
  have hs (n : ℕ) (i : Fin 2) : ∀ᵐ x ∂μ, x ∉ K → q n i x = 0 := by
    dsimp [q]
    split_ifs <;> first | exact hsg n | exact hsh n
  have ht := compact_finite_weighted_norm_sq_tendsto hK a ha hq hs
  simpa [a,q,r,Fin.sum_univ_two] using ht

theorem compact_weighted_inner_finite_tendsto {K : Set E} (hK : IsCompact K)
    (χ : E → ℝ) (hχ : Continuous χ) (ψ : I → E → ℝ) (hψ : ∀ i, Continuous (ψ i))
    {g : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ}
    {h : ℕ → I → Lp ℂ 2 μ} {k : I → Lp ℂ 2 μ}
    (hg : Tendsto g atTop (𝓝 f)) (hh : ∀ i, Tendsto (fun n => h n i) atTop (𝓝 (k i)))
    (hsg : ∀ n, ∀ᵐ x ∂μ, x ∉ K → g n x = 0)
    (hsh : ∀ n i, ∀ᵐ x ∂μ, x ∉ K → h n i x = 0) :
    Tendsto (fun n => ∫ x, inner ℝ (χ x • g n x) (∑ i, ψ i x • h n i x) ∂μ)
      atTop (𝓝 (∫ x, inner ℝ (χ x • f x) (∑ i, ψ i x • k i x) ∂μ)) := by
  have hsf := lp_ae_zero_on_of_tendsto hK.measurableSet.compl hg hsg
  have hsk (i : I) := lp_ae_zero_on_of_tendsto hK.measurableSet.compl (hh i) (fun n => hsh n i)
  have he (q : Lp ℂ 2 μ) (r : I → Lp ℂ 2 μ)
      (hsq : ∀ᵐ x ∂μ, x ∉ K → q x = 0)
      (hsr : ∀ i, ∀ᵐ x ∂μ, x ∉ K → r i x = 0) :
      inner ℝ (compactSupportWeightedL2 hK χ hχ q)
        (∑ i, compactSupportWeightedL2 hK (ψ i) (hψ i) (r i)) =
      ∫ x, inner ℝ (χ x • q x) (∑ i, ψ i x • r i x) ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [compactSupportWeightedL2_ae hK χ hχ q hsq,
      compact_finite_weighted_L2_ae hK ψ hψ r hsr] with x hx hy
    rw [hx,hy]
  have hA := compactSupportWeightedL2_tendsto hK χ hχ hg
  have hB : Tendsto (fun n => ∑ i, compactSupportWeightedL2 hK (ψ i) (hψ i) (h n i)) atTop
      (𝓝 (∑ i, compactSupportWeightedL2 hK (ψ i) (hψ i) (k i))) :=
    tendsto_finsetSum _ (fun i _ => compactSupportWeightedL2_tendsto hK (ψ i) (hψ i) (hh i))
  have ht := Filter.Tendsto.inner (𝕜 := ℝ) hA hB
  simpa only [he _ _ hsf hsk, he _ _ (hsg _) (hsh _)] using ht

end TheoremT.Continuum
