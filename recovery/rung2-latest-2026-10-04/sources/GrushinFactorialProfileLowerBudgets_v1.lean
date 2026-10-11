import GrushinFactorialLocalRepresentatives_v1

/-! One actual family of shifted weighted L2 representatives simultaneously
satisfies every lower derivative-cost profile bound. The representative
choice is made only once at the largest cutoff, independently of q. -/
noncomputable section
open MeasureTheory
namespace TheoremT.Continuum.WeakGrushin

theorem factorialLocalProfile_coherent_lower_representatives
    {D : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))} {r : ℕ}
    (h : FactorialLocalMemLp D Ω r) :
    ∃ W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex →
        Lp ℂ 2 (volume.restrict Ω),
      ∀ q, q ≤ r → ∀ a b, factorialMultiDerivativeCost a b ≤ q →
        FactorialShiftedOuterL2Rep D W a b ∧
        factorialOuterNorm (W a b) = factorialLocalOuterNorm D Ω a b ∧
        factorialOuterNorm (W a b) ≤ factorialLocalProfile D Ω q := by
  obtain ⟨W, hW⟩ := factorialLocalProfile_representatives h
  refine ⟨W, ?_⟩
  intro q hqr a b hab
  have hh := hW a b (hab.trans hqr)
  exact ⟨hh.1, hh.2.1, hh.2.1.le.trans
    (factorialLocalOuterNorm_le_profile D Ω q a b hab)⟩

end TheoremT.Continuum.WeakGrushin
