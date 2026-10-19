import GrushinFactorialLocalProfile_v1

/-! Lift a common bound on every actual outer norm to the exact finite
profile. The nonempty finite index set and its cost characterization are
proved dependencies, not additional hypotheses. Actual L2 finiteness is
supplied separately when this finite-maximum implication is applied. -/
noncomputable section
set_option autoImplicit false
namespace TheoremT.Continuum.WeakGrushin

theorem factorialLocalProfile_le_of_outerNorm_le
    {D : FactorialRawJetFamily} {Ω : Set (Space (Fin 3))} {r : ℕ} {Q : ℝ}
    (h : ∀ α β, factorialMultiDerivativeCost α β ≤ r →
      factorialLocalOuterNorm D Ω α β ≤ Q) :
    factorialLocalProfile D Ω r ≤ Q := by
  apply Finset.sup'_le
  intro b hb
  exact h b.1 b.2 ((factorialBaseIndices_mem r b).mp hb)

end TheoremT.Continuum.WeakGrushin
