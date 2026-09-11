import WeakGrushinJetFields_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem l2_norm_sq_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (f : Lp ℂ 2 μ) : ‖f‖^2 = ∫ x, ‖f x‖^2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq,L2.inner_def]
  simp only [real_inner_self_eq_norm_sq]

theorem l2_integral_norm_sq_tendsto {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {g : ℕ → Lp ℂ 2 μ} {f : Lp ℂ 2 μ} (hg : Tendsto g atTop (𝓝 f)) :
    Tendsto (fun n => ∫ x, ‖g n x‖^2 ∂μ) atTop (𝓝 (∫ x, ‖f x‖^2 ∂μ)) := by
  simpa only [l2_norm_sq_integral] using hg.norm.pow 2

theorem principal_norm_sq_tendsto (c : ℝ)
    {K : Set (Space κ)} (hK : IsCompact K) {g : ℕ → Jet κ} {f : Jet κ}
    (hg : ∀ v w, Tendsto (fun n => g n v w) atTop (𝓝 (f v w)))
    (hs : ∀ n v w, ∀ᵐ p ∂volume, p ∉ K → g n v w p = 0) :
    Tendsto (fun n => ∫ p, ‖principal c (g n) p‖^2) atTop
      (𝓝 (∫ p, ‖principal c f p‖^2)) := by
  have hd (i : Fin 4 ⊕ κ) :
      Tendsto (fun n => diagonalJet (g n) i) atTop (𝓝 (diagonalJet f i)) := by
    cases i with
    | inl i => exact hg (yDir i) (yDir i)
    | inr j => exact hg (tDir j) (tDir j)
  have hds (n : ℕ) (i : Fin 4 ⊕ κ) :
      ∀ᵐ p ∂volume, p ∉ K → diagonalJet (g n) i p = 0 := by
    cases i with
    | inl i => exact hs n (yDir i) (yDir i)
    | inr j => exact hs n (tDir j) (tDir j)
  have hh := compact_finite_weighted_norm_sq_tendsto hK
    (principalWeight c) (principalWeight_continuous c) hd hds
  simpa only [← principal_eq_finite_weighted] using hh

theorem principal_memLp (c : ℝ) {K : Set (Space κ)} (hK : IsCompact K) (f : Jet κ)
    (hs : ∀ v w, ∀ᵐ p ∂volume, p ∉ K → f v w p = 0) :
    MemLp (principal c f) 2 volume := by
  have hds (i : Fin 4 ⊕ κ) :
      ∀ᵐ p ∂volume, p ∉ K → diagonalJet f i p = 0 := by
    cases i with
    | inl i => exact hs (yDir i) (yDir i)
    | inr j => exact hs (tDir j) (tDir j)
  have hh := compact_finite_weighted_memLp hK
    (principalWeight c) (principalWeight_continuous c) (diagonalJet f) hds
  simpa only [← principal_eq_finite_weighted] using hh

theorem tWeighted_norm_sq_tendsto (c : ℝ)
    {K : Set (Space κ)} (hK : IsCompact K) {g : ℕ → Jet κ} {f : Jet κ}
    (hg : ∀ v w, Tendsto (fun n => g n v w) atTop (𝓝 (f v w)))
    (hs : ∀ n v w, ∀ᵐ p ∂volume, p ∉ K → g n v w p = 0) :
    Tendsto (fun n => ∫ p, ‖tWeighted c (g n) p‖^2) atTop
      (𝓝 (∫ p, ‖tWeighted c f p‖^2)) := by
  have hh := compact_finite_weighted_norm_sq_tendsto hK
    (fun (_ : κ) (p : Space κ) => c*‖p.1‖^2) (fun _ => by fun_prop)
    (fun j => hg (tDir j) (tDir j)) (fun n j => hs n (tDir j) (tDir j))
  simpa only [← Finset.smul_sum,tWeighted] using hh

theorem yHessian_norm_sq_tendsto {g : ℕ → Jet κ} {f : Jet κ}
    (hg : ∀ v w, Tendsto (fun n => g n v w) atTop (𝓝 (f v w))) :
    Tendsto (fun n => ∑ i : Fin 4, ∑ j : Fin 4, ∫ p, ‖g n (yDir i) (yDir j) p‖^2)
      atTop (𝓝 (∑ i : Fin 4, ∑ j : Fin 4, ∫ p, ‖f (yDir i) (yDir j) p‖^2)) :=
  tendsto_finsetSum _ (fun i _ => tendsto_finsetSum _
    (fun j _ => l2_integral_norm_sq_tendsto (hg (yDir i) (yDir j))))

theorem tGradient_norm_sq_tendsto
    {g : ℕ → Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    {f : Space κ → Lp ℂ 2 (volume : Measure (Space κ))}
    (hg : ∀ v, Tendsto (fun n => g n v) atTop (𝓝 (f v))) :
    Tendsto (fun n => ∑ j : κ, ∫ p, ‖g n (tDir j) p‖^2) atTop
      (𝓝 (∑ j : κ, ∫ p, ‖f (tDir j) p‖^2)) :=
  tendsto_finsetSum _ (fun j _ => l2_integral_norm_sq_tendsto (hg (tDir j)))

theorem mixed_norm_sq_tendsto
    {K : Set (Space κ)} (hK : IsCompact K) {g : ℕ → Jet κ} {f : Jet κ}
    (hg : ∀ v w, Tendsto (fun n => g n v w) atTop (𝓝 (f v w)))
    (hs : ∀ n v w, ∀ᵐ p ∂volume, p ∉ K → g n v w p = 0) :
    Tendsto (fun n => ∑ i : Fin 4, ∑ j : κ, ∫ p, ‖p.1‖^2 * ‖g n (yDir i) (tDir j) p‖^2)
      atTop (𝓝 (∑ i : Fin 4, ∑ j : κ, ∫ p, ‖p.1‖^2 * ‖f (yDir i) (tDir j) p‖^2)) := by
  apply tendsto_finsetSum _ (fun i _ => ?_)
  apply tendsto_finsetSum _ (fun j _ => ?_)
  have hh := compact_support_weight_norm_sq_tendsto hK (fun p : Space κ => ‖p.1‖)
    (by fun_prop) (hg (yDir i) (tDir j)) (fun n => hs n (yDir i) (tDir j))
  simpa only [norm_smul,Real.norm_eq_abs,abs_norm,mul_pow] using hh

end TheoremT.Continuum.WeakGrushin
