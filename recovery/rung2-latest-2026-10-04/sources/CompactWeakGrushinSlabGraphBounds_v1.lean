import CompactWeakGrushinEnergy_v1
import WeakSlabPoincare_v1
import NonnegativeEnergySlabBound_v1

/-! Actual compact weak Grushin graph bounds. The original limiting function
supplies the slab radius; no approximation-support radius enters the constant.
The output is the L2 function in the original compact-test equation, and the
weak first and second derivative witnesses remain explicit hypotheses. -/
noncomputable section
open MeasureTheory
open scoped ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_weakH2_slab_graph_bounds_output {c : ℝ} (hc : 0 ≤ c)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    (i : Fin 4) {R : ℝ} (hR : 0 < R)
    (hslab : ∀ᵐ p ∂volume, f p ≠ 0 → |p.1 i| ≤ R) :
    ‖f‖^2 ≤ (4*R^2)^2*‖h‖^2 ∧
      weakGrushinGradientEnergy c d ≤ (4*R^2)*‖h‖^2 ∧
      (∑ j : Fin 4, ∫ p, ‖d (yDir j) p‖^2) ≤ (4*R^2)*‖h‖^2 := by
  have hY := weakGrushin_y_gradient_le_energy hc d
  have hi : (∫ p, ‖d (yDir i) p‖^2) ≤ weakGrushinGradientEnergy c d := by
    apply le_trans _ hY
    exact Finset.single_le_sum (f := fun j : Fin 4 => ∫ p : Space κ, ‖d (yDir j) p‖^2)
      (fun _ _ => integral_nonneg (fun _ => sq_nonneg _)) (Finset.mem_univ i)
  have hsG : ‖f‖^2 ≤ (4*R^2)*weakGrushinGradientEnergy c d := by
    rw [l2_norm_sq_integral f]
    exact (compact_weakH2_y_slab_poincare_integral d e hd he hK hs i hR hslab).trans
      (mul_le_mul_of_nonneg_left hi (show 0 ≤ 4*R^2 from by positivity))
  obtain ⟨hinput,henergy⟩ := nonnegative_energy_slab_bounds
    (‖f‖^2) (weakGrushinGradientEnergy c d) (‖h‖^2) (4*R^2)
    (weakGrushinGradientEnergy_nonneg hc d) (sq_nonneg _) (by positivity) hsG
    (compact_weakH2_energy_output c d e hd he hK hs hP).2
  exact ⟨hinput,henergy,hY.trans henergy⟩

theorem compact_weakH2_slab_graph_bounds_on_compact {c : ℝ} (hc : 0 ≤ c)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    (i : Fin 4) {R : ℝ} (hR : 0 < R) (hslab : ∀ p ∈ K, |p.1 i| ≤ R) :
    ‖f‖^2 ≤ (4*R^2)^2*‖h‖^2 ∧
      weakGrushinGradientEnergy c d ≤ (4*R^2)*‖h‖^2 ∧
      (∑ j : Fin 4, ∫ p, ‖d (yDir j) p‖^2) ≤ (4*R^2)*‖h‖^2 := by
  apply compact_weakH2_slab_graph_bounds_output hc d e hd he hK hs hP i hR
  filter_upwards [hs] with p hp hne
  exact hslab p (by by_contra hnot; exact hne (hp hnot))

end TheoremT.Continuum.WeakGrushin
