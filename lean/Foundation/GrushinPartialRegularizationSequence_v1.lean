import GrushinPartialMollifierH2_v1

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff
namespace TheoremT.Continuum
variable {T : Type*} [NormedAddCommGroup T] [InnerProductSpace ℝ T]
  [FiniteDimensional ℝ T] [MeasurableSpace T] [BorelSpace T]
variable {κ : Type*} [Fintype κ]

theorem grushin_partial_regularization_sequence
    (c : ℝ) (b : OrthonormalBasis κ ℝ T) {Ω C U : Set (KSSpace × T)}
    (hΩ : IsOpen Ω) (hC : IsCompact C) (hCΩ : C ⊆ Ω) (hU : IsOpen U) (hUC : U ⊆ C)
    (G h : Lp ℂ 2 (volume : Measure (KSSpace × T)))
    (hweak : ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, splitGrushin c b (fun _ => 0) φ p • G p) = ∫ p, φ p • h p) :
    (∀ n : ℕ, ‖partialMollifyLp n G‖ ≤ ‖G‖ ∧ ‖partialMollifyLp n h‖ ≤ ‖h‖) ∧
    Tendsto (fun n : ℕ => partialMollifyLp n G) atTop (𝓝 G) ∧
    Tendsto (fun n : ℕ => partialMollifyLp n h) atTop (𝓝 h) ∧
    ∀ᶠ n : ℕ in atTop,
      ProductLocalWeakH2On (partialMollifyLp n G : KSSpace × T → ℂ) U ∧
      ∀ φ : KSSpace × T → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ U →
        (∫ p, splitGrushin c b (fun _ => 0) φ p • partialMollifyLp n G p) =
          ∫ p, φ p • partialMollifyLp n h p := by
  exact ⟨(fun n => ⟨partialMollifyLp_norm_le n G,partialMollifyLp_norm_le n h⟩),
    partialMollifyLp_tendsto G,partialMollifyLp_tendsto h,
    partialMollifyLp_local_h2_and_weak_equation_eventually c b hΩ hC hCΩ hU hUC G h hweak⟩

#print axioms grushin_partial_regularization_sequence
end TheoremT.Continuum
