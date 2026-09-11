import WeakGrushinSpectatorDifferentiate_v1

/-! Genuine L2 representative specialization of local spectator commutation.
One weak L2 derivative of G is sufficient; no second derivative of G is input. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem weak_grushin_spectator_differentiate (c : ℝ)
    {Ω : Set (Space κ)} {G d : Lp ℂ 2 (volume : Measure (Space κ))}
    (h k : Space κ → ℂ)
    (hh : ProductLocallyL2On h Ω) (hk : ProductLocallyL2On k Ω)
    (v : EuclideanSpace ℝ κ) (hD : WeakProductL2Directional G d (0,v))
    (hP : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • G p) = ∫ p, φ p • h p)
    (hhD : ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • k p) = -(∫ p, fderiv ℝ φ p (0,v) • h p)) :
    ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • d p) = ∫ p, φ p • k p := by
  have hGl : ProductLocallyL2On (G : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp G).mono_measure Measure.restrict_le_self
  have hdl : ProductLocallyL2On (d : Space κ → ℂ) Ω :=
    fun _ _ _ => (Lp.memLp d).mono_measure Measure.restrict_le_self
  intro φ hφ hcφ hsφ
  exact (local_weak_grushin_spectator_differentiate c G d h k hGl hdl hh hk v
    (fun φ hφ hcφ _ => hD φ hφ hcφ) hP hhD φ hφ hcφ hsφ).2.2

#print axioms weak_grushin_spectator_differentiate
end TheoremT.Continuum.WeakGrushin
