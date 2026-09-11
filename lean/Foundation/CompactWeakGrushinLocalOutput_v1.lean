import CompactWeakGrushinCaccioppoli_v1

/-! Cutoff energy and Caccioppoli use a supplied weak PDE only on the open
region containing the cutoff support. The output outside that region is irrelevant. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem compact_weakH2_cutoff_energy_local_output (c : ℝ)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) (hηΩ : tsupport η ⊆ Ω)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    cutoffGradient c η f d =
      (∫ p, inner ℝ ((η p)^2 • f p) (h p)) + grushinCutoffEnergy c η f := by
  have ha := principal_ae_eq_of_weak_output_local c d e hd he hΩ hP
  have hpair : (∫ p, inner ℝ ((η p)^2 • f p) (principal c e p)) =
      ∫ p, inner ℝ ((η p)^2 • f p) (h p) := by
    apply integral_congr_ae
    filter_upwards [ha] with p hp
    by_cases hpo : p ∈ Ω
    · rw [hp hpo]
    · have hz : η p = 0 := image_eq_zero_of_notMem_tsupport (fun ht => hpo (hηΩ ht))
      simp only [hz,zero_pow (by decide : 2 ≠ 0),zero_smul,inner_zero_left]
  rw [compact_weakH2_cutoff_energy c hη hcη d e hd he hK hs,hpair]

theorem compact_weakH2_cutoff_caccioppoli_local_output (c : ℝ)
    {η : Space κ → ℝ} (hη : ContDiff ℝ ∞ η) (hcη : HasCompactSupport η)
    {f h : Lp ℂ 2 (volume : Measure (Space κ))}
    (d : Space κ → Lp ℂ 2 (volume : Measure (Space κ))) (e : Jet κ)
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space κ)} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω) (hηΩ : tsupport η ⊆ Ω)
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p) :
    cutoffGradient c η f d ≤
      ((∫ p, (η p)^2*‖f p‖^2)+(∫ p, (η p)^2*‖h p‖^2))/2 +
        grushinCutoffEnergy c η f := by
  rw [compact_weakH2_cutoff_energy_local_output c hη hcη d e hd he hK hs hΩ hηΩ hP]
  exact add_le_add (cutoff_l2_pairing_le_half hη.continuous hcη f (Lp.memLp h)) (le_refl _)

end TheoremT.Continuum.WeakGrushin
