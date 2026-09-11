import FreeResolvent_v1

/-!
Independently compiled mathematical expansion of the free resolvent claims.
The successful v1 pp.all audit remains preserved: it expanded implementation
typeclass data to 134 MB while still eliding subterms. This audit instead
spells out the physical spaces, Fourier symbol, and every weak-test premise.
Proof terms and normed-space instance implementation are not part of the
mathematical statements and are not bulk printed.
-/

noncomputable section
open MeasureTheory FourierTransform
open scoped ContDiff BigOperators

namespace TheoremT.Continuum.ResolventAudit

theorem actual_fourier_symbol (N : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) :
    𝓕 (freeResolvent N μ hμ f) =ᵐ[volume]
      fun ξ => (((2 * Real.pi^2 * ‖ξ‖^2 + μ)⁻¹ : ℝ) : ℂ) * (𝓕 f) ξ := by
  simpa only [freeResolventSymbol, freeKineticSymbol] using
    freeResolvent_fourier_ae N hμ f

theorem actual_resolvent_norm (N : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    ‖(freeResolvent N μ hμ :
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ≤ μ⁻¹ :=
  norm_freeResolvent_le N hμ

theorem actual_kinetic_output_norm (N : ℕ) (μ : ℝ) (hμ : 0 < μ) :
    ‖(freeKineticResolvent N μ hμ :
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))) →L[ℂ]
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))))‖ ≤ 1 :=
  norm_freeKineticResolvent_le N hμ

theorem actual_weak_H2_shifted_equation (N : ℕ) (μ : ℝ) (hμ : 0 < μ)
    (f : Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3)))) :
    ∃ d : (Fin N × Fin 3) →
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))),
    ∃ e : (Fin N × Fin 3) → (Fin N × Fin 3) →
      Lp ℂ 2 (volume : Measure (EuclideanSpace ℝ (Fin N × Fin 3))),
      (∀ k, ∀ φ : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ,
        ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x, φ x • (d k) x) =
          -(∫ x, (fderiv ℝ φ x (PiLp.single 2 k 1)) •
            (freeResolvent N μ hμ f) x)) ∧
      (∀ k l, ∀ φ : EuclideanSpace ℝ (Fin N × Fin 3) → ℝ,
        ContDiff ℝ ∞ φ → HasCompactSupport φ →
        (∫ x, φ x • (e k l) x) =
          -(∫ x, (fderiv ℝ φ x (PiLp.single 2 l 1)) • (d k) x)) ∧
      f = (-((1 : ℝ) / 2)) • (∑ k, e k k) +
        μ • freeResolvent N μ hμ f :=
  freeResolvent_solve N hμ f

#print actual_fourier_symbol
#print actual_resolvent_norm
#print actual_kinetic_output_norm
#print actual_weak_H2_shifted_equation
#print TheoremT.Continuum.freeResolvent
#print TheoremT.Continuum.freeKineticResolvent
#print TheoremT.Continuum.fourierConjugateL2
#print TheoremT.Continuum.spatialL2BoundedMultiplier
#print axioms actual_fourier_symbol
#print axioms actual_resolvent_norm
#print axioms actual_kinetic_output_norm
#print axioms actual_weak_H2_shifted_equation

end TheoremT.Continuum.ResolventAudit
