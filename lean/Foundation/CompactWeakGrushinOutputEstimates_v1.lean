import WeakGrushinPrincipalTests_v1
import CompactWeakGrushinEstimates_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem principal_ae_eq_of_weak_output_local (c : ℝ)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    ∀ᵐ p ∂volume, p ∈ Ω → principal c e p = h p := by
  have hfli := principal_locallyIntegrable c e
  have hhli := (Lp.memLp h).locallyIntegrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hz : ∀ᵐ p ∂volume, p ∈ Ω → principal c e p - h p = 0 := by
    apply hΩ.ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hfli.sub hhli).locallyIntegrableOn Ω)
    intro φ hφ hc hs
    simp only [Pi.sub_apply,smul_sub]
    rw [integral_sub
      (hfli.integrable_smul_left_of_hasCompactSupport hφ.continuous hc)
      (hhli.integrable_smul_left_of_hasCompactSupport hφ.continuous hc),
      principal_compact_test c d e hd he hφ hc,hP φ hφ hc hs,sub_self]
  filter_upwards [hz] with p hp hpin
  exact sub_eq_zero.mp (hp hpin)

theorem compact_weakH2_output_estimates {c : ℝ} (hc0 : 0 ≤ c)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    (principal c e =ᵐ[volume] h) ∧
    ((16*c)*(∑ j : κ, ∫ p, ‖d (tDir j) p‖^2) ≤ ‖h‖^2) ∧
    ((∑ i : Fin 4, ∑ j : Fin 4, ∫ p, ‖e (yDir i) (yDir j) p‖^2) +
      (∫ p, ‖tWeighted c e p‖^2) +
      2*c*(∑ i : Fin 4, ∑ j : κ, ∫ p, ‖p.1‖^2 * ‖e (yDir i) (tDir j) p‖^2) ≤
        (3/2 : ℝ)*‖h‖^2) := by
  have ha := principal_ae_eq_of_weak_output c d e hd he hP
  have hn : (∫ p, ‖principal c e p‖^2) = ‖h‖^2 := by
    rw [l2_norm_sq_integral]
    apply integral_congr_ae
    filter_upwards [ha] with p hp
    rw [hp]
  obtain ⟨_,ht,hfull⟩ := compact_weakH2_estimates hc0 d e hd he hK hs
  exact ⟨ha,by simpa only [hn] using ht,by simpa only [hn] using hfull⟩

end TheoremT.Continuum.WeakGrushin
