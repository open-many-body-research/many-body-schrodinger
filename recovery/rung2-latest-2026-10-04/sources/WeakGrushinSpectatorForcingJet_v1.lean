import WeakGrushinPotentialDerivative_v1
import WeakGrushinJetFields_v1

/-! Actual first spectator derivatives of the differentiated homogeneous
potential forcing. These are obtained from the given first derivatives of G;
no second derivative of G or derivative of dT is an input assumption. -/
noncomputable section
open MeasureTheory
open scoped ContDiff
namespace TheoremT.Continuum.WeakGrushin
variable {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spectator_potential_coefficient_contDiffOn
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω) (j : κ) :
    ContDiffOn ℝ ∞ (fun p => fderiv ℝ B p (tDir j)) Ω := by
  intro p hp
  exact (local_contDiffAt_directional_derivative
    (hB.contDiffAt (hΩ.mem_nhds hp)) (tDir j)).contDiffWithinAt

theorem spectator_potential_forcing_jet
    {Ω : Set (Space κ)} (hΩ : IsOpen Ω)
    {B : Space κ → ℝ} (hB : ContDiffOn ℝ ∞ B Ω)
    (G : Lp ℂ 2 (volume : Measure (Space κ)))
    (dT : κ → Lp ℂ 2 (volume : Measure (Space κ)))
    (hdT : ∀ k, WeakProductL2Directional G (dT k) (tDir k)) (j : κ) :
    ProductLocallyL2On (fun p => -(fderiv ℝ B p (tDir j) • G p)) Ω ∧
    (∀ k, ProductLocallyL2On (fun p =>
      -(fderiv ℝ B p (tDir j) • dT k p +
        fderiv ℝ (fun q => fderiv ℝ B q (tDir j)) p (tDir k) • G p)) Ω) ∧
    ∀ k, ∀ φ : Space κ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ω →
      (∫ p, φ p • (-(fderiv ℝ B p (tDir j) • dT k p +
        fderiv ℝ (fun q => fderiv ℝ B q (tDir j)) p (tDir k) • G p))) =
        -(∫ p, fderiv ℝ φ p (tDir k) • (-(fderiv ℝ B p (tDir j) • G p))) := by
  have hC := spectator_potential_coefficient_contDiffOn hΩ hB j
  have hbase := product_smooth_coefficient_locallyL2 hΩ hC G
  have hL (k : κ) := weakProduct_spectator_local_potential_leibniz (hdT k) hΩ hC
  refine ⟨(fun K hK hKO => (hbase K hK hKO).neg),?_,?_⟩
  · intro k K hK hKO
    exact ((hL k).2.1 K hK hKO).neg
  · intro k φ hφ hcφ hsφ
    have he := (hL k).2.2 φ hφ hcφ hsφ
    simpa only [tDir,smul_neg,integral_neg,neg_neg] using congrArg Neg.neg he.2.2

#print axioms spectator_potential_coefficient_contDiffOn
#print axioms spectator_potential_forcing_jet
end TheoremT.Continuum.WeakGrushin
