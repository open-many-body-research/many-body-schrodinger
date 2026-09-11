import WeakGrushinAnisotropicLimitOutput_v1

/-! Eventual existence of actual compact weak Grushin outputs suffices.
The chosen output sequence is only an analytic witness; no executable
selection algorithm is asserted. Its values away from good indices may be
zero and play no role in the eventual hypotheses or conclusion.
-/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff BigOperators
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem anisotropic_limit_of_eventually_exists_compact_outputs
    {c : ℝ} (hc : 0 < c)
    (u : ℕ → Lp ℂ 2 (volume : Measure (Space κ)))
    (f : Lp ℂ 2 (volume : Measure (Space κ))) (hf : Tendsto u atTop (𝓝 f))
    {F M : ℝ}
    (ha : ∀ᶠ n : ℕ in atTop,
      ∃ H : Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
      ∃ e : Jet κ, ∃ K : Set (Space κ),
        (∀ v, WeakProductL2Directional (u n) (d v) v) ∧
        (∀ v w, WeakProductL2Directional (d v) (e v w) w) ∧
        IsCompact K ∧ (∀ᵐ p ∂volume, p ∉ K → u n p = 0) ∧
        (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • u n p) =
            ∫ p, φ p • H p) ∧
        ‖u n‖^2 ≤ F ∧ ‖H‖^2 ≤ M) :
    ∃ gy : Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ gt : κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ hyy : Fin 4 → Fin 4 → Lp ℂ 2 (volume : Measure (Space κ)),
      (∑ i, ‖gy i‖^2) ≤ 2*F+(3/4 : ℝ)*M ∧
      (∑ j, ‖gt j‖^2) ≤ M/(16*c) ∧
      (∑ i, ∑ j, ‖hyy i j‖^2) ≤ (3/2 : ℝ)*M ∧
      (∀ i, WeakProductL2Directional f (gy i) (yDir i)) ∧
      (∀ j, WeakProductL2Directional f (gt j) (tDir j)) ∧
      ∀ i j, WeakProductL2Directional (gy i) (hyy i j) (yDir j) := by
  classical
  let Good (n : ℕ) (H : Lp ℂ 2 (volume : Measure (Space κ))) : Prop :=
    ∃ d : Space κ → Lp ℂ 2 (volume : Measure (Space κ)),
    ∃ e : Jet κ, ∃ K : Set (Space κ),
      (∀ v, WeakProductL2Directional (u n) (d v) v) ∧
      (∀ v w, WeakProductL2Directional (d v) (e v w) w) ∧
      IsCompact K ∧ (∀ᵐ p ∂volume, p ∉ K → u n p = 0) ∧
      (∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • u n p) =
          ∫ p, φ p • H p) ∧
      ‖u n‖^2 ≤ F ∧ ‖H‖^2 ≤ M
  have hAll : ∀ n, ∃ H, (∃ H, Good n H) → Good n H := by
    intro n
    by_cases hn : ∃ H, Good n H
    · exact ⟨hn.choose,fun _ => hn.choose_spec⟩
    · exact ⟨0,fun hx => False.elim (hn hx)⟩
  choose H hH using hAll
  have heventual : ∀ᶠ n : ℕ in atTop, Good n (H n) := by
    filter_upwards [ha] with n hn
    exact hH n hn
  exact anisotropic_limit_of_eventual_compact_weakH2_outputs hc u H f hf heventual

#print axioms anisotropic_limit_of_eventually_exists_compact_outputs
end TheoremT.Continuum.WeakGrushin
