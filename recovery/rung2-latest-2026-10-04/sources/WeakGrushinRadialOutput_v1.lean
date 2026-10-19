import WeakGrushinRadialJetBounds_v1
import ProductWeakJetClosedSupport_v1

/-! The radial maximal estimates identify the actual weak output. All
weighted fields are genuine L2 functions supported on the original compact
set, not merely finite Bochner integrals of possibly nonintegrable fields. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_weakH2_weighted_jet_memLp
    {f : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0) :
    (∀ v, ∀ᵐ p ∂volume, p ∉ K → d v p = 0) ∧
    (∀ v w, ∀ᵐ p ∂volume, p ∉ K → e v w p = 0) ∧
    (∀ (χ : Space κ → ℝ), Continuous χ → ∀ v,
      MemLp (fun p => χ p • d v p) 2 volume) ∧
    (∀ (χ : Space κ → ℝ), Continuous χ → ∀ v w,
      MemLp (fun p => χ p • e v w p) 2 volume) := by
  have hds (v) := weakProductL2Directional_closed_support (hd v) hK.isClosed hs
  have hes (v w) := weakProductL2Second_closed_support (hd v) (he v w) hK.isClosed hs
  exact ⟨hds,hes,
    fun χ hχ v => compact_support_weight_memLp hK χ hχ (d v) (hds v),
    fun χ hχ v w => compact_support_weight_memLp hK χ hχ (e v w) (hes v w)⟩

theorem compact_weakH2_radial_output_estimates {c : ℝ} (hc : 0 ≤ c)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    (principal c e =ᵐ[volume] h) ∧
    (∀ j : κ, 16*c*(∫ p, ‖d (tDir j) p‖^2) ≤ ‖h‖^2) ∧
    (∀ i j : Fin 4, (∫ p, ‖e (yDir i) (yDir j) p‖^2) ≤ (3/2 : ℝ)*‖h‖^2) ∧
    (∀ (i : Fin 4) (j : κ),
      2*c*(∫ p, ‖‖p.1‖ • e (yDir i) (tDir j) p‖^2) ≤ (3/2 : ℝ)*‖h‖^2) ∧
    (∀ i j : κ,
      c^2*(∫ p, ‖(‖p.1‖^2) • e (tDir i) (tDir j) p‖^2) ≤ (3/2 : ℝ)*‖h‖^2) := by
  have ha := principal_ae_eq_of_weak_output c d e hd he hP
  have hn : (∫ p, ‖principal c e p‖^2) = ‖h‖^2 := by
    rw [l2_norm_sq_integral]
    exact integral_congr_ae (ha.fun_comp (fun z : ℂ => ‖z‖^2))
  exact ⟨ha,by simpa only [hn] using compact_weakH2_radial_estimates hc d e hd he hK hs⟩

end TheoremT.Continuum.WeakGrushin
