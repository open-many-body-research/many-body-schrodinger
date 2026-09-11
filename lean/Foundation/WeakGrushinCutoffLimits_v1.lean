import CompactWeightedPairLimits_v1
import WeakGrushinJetLimits_v1
import GrushinCutoffEnergy_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

def cutoffDirectional (η : Space κ → ℝ) (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (v p : Space κ) : ℂ :=
  η p • d v p + fderiv ℝ η p v • f p

def cutoffGradient (c : ℝ) (η : Space κ → ℝ) (f : Lp ℂ 2 (volume : Measure (Space κ)))
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) : ℝ :=
  (∑ i : Fin 4, ∫ p, ‖cutoffDirectional η f d (yDir i) p‖^2) +
    c*(∑ j : κ, ∫ p, ‖p.1‖^2*‖cutoffDirectional η f d (tDir j) p‖^2)

theorem cutoffDirectional_norm_sq_tendsto
    {K : Set (Space κ)} (hK : IsCompact K) {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η)
    (ρ : Space κ → ℝ) (hρ : Continuous ρ)
    {g : ℕ → Lp ℂ 2 (volume : Measure (Space κ))} {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {a : ℕ → Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hg : Tendsto g atTop (𝓝 f)) (ha : ∀ v, Tendsto (fun n => a n v) atTop (𝓝 (d v)))
    (hsg : ∀ n, ∀ᵐ p ∂volume, p ∉ K → g n p = 0)
    (hsa : ∀ n v, ∀ᵐ p ∂volume, p ∉ K → a n v p = 0) (v : Space κ) :
    Tendsto (fun n => ∫ p, ‖ρ p • cutoffDirectional η (g n) (a n) v p‖^2) atTop
      (𝓝 (∫ p, ‖ρ p • cutoffDirectional η f d v p‖^2)) := by
  have hdη : Continuous (fun p => fderiv ℝ η p v) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have ht := compact_two_weighted_norm_sq_tendsto hK
    (fun p => ρ p*η p) (fun p => ρ p*fderiv ℝ η p v)
    (hρ.mul hη.continuous) (hρ.mul hdη) (ha v) hg (fun n => hsa n v) hsg
  simpa only [cutoffDirectional,smul_add,mul_smul] using ht

theorem cutoffGradient_tendsto (c : ℝ)
    {K : Set (Space κ)} (hK : IsCompact K) {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η)
    {g : ℕ → Lp ℂ 2 (volume : Measure (Space κ))} {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {a : ℕ → Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hg : Tendsto g atTop (𝓝 f)) (ha : ∀ v, Tendsto (fun n => a n v) atTop (𝓝 (d v)))
    (hsg : ∀ n, ∀ᵐ p ∂volume, p ∉ K → g n p = 0)
    (hsa : ∀ n v, ∀ᵐ p ∂volume, p ∉ K → a n v p = 0) :
    Tendsto (fun n => cutoffGradient c η (g n) (a n)) atTop (𝓝 (cutoffGradient c η f d)) := by
  have hY (i : Fin 4) : Tendsto
      (fun n => ∫ p, ‖cutoffDirectional η (g n) (a n) (yDir i) p‖^2) atTop
      (𝓝 (∫ p, ‖cutoffDirectional η f d (yDir i) p‖^2)) := by
    simpa only [one_smul] using cutoffDirectional_norm_sq_tendsto hK hη
      (fun _ => 1) continuous_const hg ha hsg hsa (yDir i)
  have hT (j : κ) : Tendsto
      (fun n => ∫ p, ‖p.1‖^2*‖cutoffDirectional η (g n) (a n) (tDir j) p‖^2) atTop
      (𝓝 (∫ p, ‖p.1‖^2*‖cutoffDirectional η f d (tDir j) p‖^2)) := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_norm,mul_pow] using
      cutoffDirectional_norm_sq_tendsto hK hη (fun p => ‖p.1‖) (by fun_prop)
        hg ha hsg hsa (tDir j)
  exact (tendsto_finsetSum _ (fun i _ => hY i)).add
    ((tendsto_finsetSum _ (fun j _ => hT j)).const_mul c)

theorem cutoffError_tendsto (c : ℝ)
    {K : Set (Space κ)} (hK : IsCompact K) {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η)
    {g : ℕ → Lp ℂ 2 (volume : Measure (Space κ))} {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (hg : Tendsto g atTop (𝓝 f))
    (hsg : ∀ n, ∀ᵐ p ∂volume, p ∉ K → g n p = 0) :
    Tendsto (fun n => grushinCutoffEnergy c η (g n)) atTop (𝓝 (grushinCutoffEnergy c η f)) := by
  have hD (v : Space κ) : Continuous (fun p => fderiv ℝ η p v) :=
    (hη.continuous_fderiv (by simp)).clm_apply continuous_const
  have hY (i : Fin 4) : Tendsto
      (fun n => ∫ p, ‖partialYDirectional η (oscillatorBasis i) p • g n p‖^2) atTop
      (𝓝 (∫ p, ‖partialYDirectional η (oscillatorBasis i) p • f p‖^2)) :=
    compact_support_weight_norm_sq_tendsto hK _ (hD (yDir i)) hg hsg
  have hT (j : κ) : Tendsto
      (fun n => ∫ p, ‖p.1‖^2*‖partialTDirectional η (oscillatorBasis j) p • g n p‖^2) atTop
      (𝓝 (∫ p, ‖p.1‖^2*‖partialTDirectional η (oscillatorBasis j) p • f p‖^2)) := by
    have ht := compact_support_weight_norm_sq_tendsto hK
      (fun p => ‖p.1‖ * fderiv ℝ η p (tDir j))
      (continuous_fst.norm.mul (hD (tDir j))) hg hsg
    simpa only [partialTDirectional,tDir,mul_smul,norm_smul,Real.norm_eq_abs,abs_norm,mul_pow] using ht
  exact (tendsto_finsetSum _ (fun i _ => hY i)).add
    ((tendsto_finsetSum _ (fun j _ => hT j)).const_mul c)

theorem cutoffPrincipalPairing_tendsto (c : ℝ)
    {K : Set (Space κ)} (hK : IsCompact K) {η : Space κ → ℝ} (hη : Continuous η)
    {g : ℕ → Lp ℂ 2 (volume : Measure (Space κ))} {f : Lp ℂ 2 (volume : Measure (Space κ))}
    {a : ℕ → Jet κ} {e : Jet κ}
    (hg : Tendsto g atTop (𝓝 f)) (ha : ∀ v w, Tendsto (fun n => a n v w) atTop (𝓝 (e v w)))
    (hsg : ∀ n, ∀ᵐ p ∂volume, p ∉ K → g n p = 0)
    (hsa : ∀ n v w, ∀ᵐ p ∂volume, p ∉ K → a n v w p = 0) :
    Tendsto (fun n => ∫ p, inner ℝ ((η p)^2 • g n p) (principal c (a n) p)) atTop
      (𝓝 (∫ p, inner ℝ ((η p)^2 • f p) (principal c e p))) := by
  have had (i : Fin 4 ⊕ κ) :
      Tendsto (fun n => diagonalJet (a n) i) atTop (𝓝 (diagonalJet e i)) := by
    cases i with
    | inl i => exact ha (yDir i) (yDir i)
    | inr j => exact ha (tDir j) (tDir j)
  have has (n : ℕ) (i : Fin 4 ⊕ κ) :
      ∀ᵐ p ∂volume, p ∉ K → diagonalJet (a n) i p = 0 := by
    cases i with
    | inl i => exact hsa n (yDir i) (yDir i)
    | inr j => exact hsa n (tDir j) (tDir j)
  have ht := compact_weighted_inner_finite_tendsto hK (fun p => (η p)^2) (hη.pow 2)
    (principalWeight c) (principalWeight_continuous c) hg had hsg has
  simpa only [← principal_eq_finite_weighted] using ht

end TheoremT.Continuum.WeakGrushin
