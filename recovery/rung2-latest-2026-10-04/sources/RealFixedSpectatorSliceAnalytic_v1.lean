import HomogeneousSpectatorRealDerivative_v1
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Analytic.Linear

/-! Real analyticity of the literal spatial slice at fixed real spectator
coordinates. The complex function is assumed jointly analytic; analyticity
of its desired real slice is proved using the actual coordinate embedding
and restriction of analytic scalars. This module uses the finite Pi norm;
the physical Euclidean Position transport is a separate continuation. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum
variable {d : ℕ}

theorem real_fixed_spectator_slice_analyticAt
    (F : (Fin 3 ⊕ Fin d → ℂ) → ℂ) (T : Fin d → ℝ) (X : Fin 3 → ℝ)
    (hF : AnalyticAt ℂ F (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ)))) :
    AnalyticAt ℝ
      (fun Y : Fin 3 → ℝ => F (Sum.elim (fun i => (Y i : ℂ)) (fun i => (T i : ℂ)))) X := by
  have hmap : AnalyticAt ℝ
      (fun Y : Fin 3 → ℝ => Sum.elim (fun i => (Y i : ℂ)) (fun i => (T i : ℂ))) X := by
    apply AnalyticAt.pi
    intro i
    cases i with
    | inl i =>
      exact (Complex.ofRealCLM.comp
        (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ)).analyticAt X
    | inr i => exact analyticAt_const
  exact AnalyticAt.comp_of_eq (g := F) (hF.restrictScalars (𝕜 := ℝ)) hmap rfl

theorem real_fixed_spectator_slice_analyticOnNhd
    (F : (Fin 3 ⊕ Fin d → ℂ) → ℂ) {D S : ℝ}
    (hF : AnalyticOnNhd ℂ F {z : Fin 3 ⊕ Fin d → ℂ |
      D*‖fun i : Fin 3 => z (.inl i)‖ < 1 ∧ S*‖fun i : Fin d => z (.inr i)‖ < 1})
    (T : Fin d → ℝ) (hT : S*‖T‖ < 1) :
    AnalyticOnNhd ℝ
      (fun X : Fin 3 → ℝ => F (Sum.elim (fun i => (X i : ℂ)) (fun i => (T i : ℂ))))
      {X : Fin 3 → ℝ | D*‖X‖ < 1} := by
  intro X hX
  change D*‖X‖ < 1 at hX
  apply real_fixed_spectator_slice_analyticAt F T X
  apply hF
  constructor
  · simpa only [Sum.elim_inl, finite_real_complexification_norm] using hX
  · simpa only [Sum.elim_inr, finite_real_complexification_norm] using hT

end TheoremT.Continuum
