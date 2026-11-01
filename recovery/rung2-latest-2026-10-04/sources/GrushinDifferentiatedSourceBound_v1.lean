import GrushinActualPrincipalCommutatorBound_v1
import GrushinActualPotentialCommutatorBound_v1

/-! An actual L2 representative and explicit bound for the right side of
the verified canonical differentiated weak equation. The source derivative
representative, coefficient majorants and lower shifted outer norms are
explicit inputs. This assembles the exact signed commutators; it does not
assume or prove closure of the resulting factorial recurrence.
-/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem factorial_differentiated_source_L2
    {μ : Measure (Space (Fin 3))} (c : ℝ) (F : FactorialRawJetFamily)
    (W : (Fin 4 → ℕ) → (Fin 3 → ℕ) → FactorialOuterIndex → Lp ℂ 2 μ)
    (r : ℕ) (N : ℕ → ℝ) (hN0 : ∀ k, 0 ≤ N k)
    (hW : ∀ a b, factorialMultiDerivativeCost a b ≤ r-1 → FactorialShiftedOuterL2Rep F W a b)
    (hN : ∀ k, k ≤ r-1 → ∀ a b, factorialMultiDerivativeCost a b ≤ k → factorialOuterNorm (W a b) ≤ N k)
    (B : Space (Fin 3) → ℝ) (M A : ℝ) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hBmeas : ∀ v, v.length ≤ r →
      AEStronglyMeasurable (directionalWordDeriv productCoordinateDirection B v) μ)
    (hBbound : ∀ v, v.length ≤ r → ∀ᵐ p ∂μ,
      |directionalWordDeriv productCoordinateDirection B v p| ≤
        M*A^v.length*(v.length.factorial : ℝ))
    (s : Space (Fin 3) → ℂ) (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (hc : factorialMultiDerivativeCost α β ≤ r)
    (HS : Lp ℂ 2 μ) (S0 : ℝ)
    (hS : HS =ᵐ[μ] complexDirectionalWordDeriv productCoordinateDirection s (mixedMultiIndexWord α β))
    (hSn : ‖HS‖ ≤ S0) :
    ∃ H : Lp ℂ 2 μ, H =ᵐ[μ] mixedMultiIndexGrushinSource c B F s α β ∧
      ‖H‖ ≤ S0+
        M*(∑ j ∈ Finset.range r, (r.choose (j+1) : ℝ)*A^(j+1)*
          ((j+1).factorial : ℝ)*N (r-(j+1)))+
        (6*|c| *(r : ℝ)*N (r-1)+3*|c| *((r*(r-1) : ℕ) : ℝ)*N (r-2)) := by
  obtain ⟨HP,hP,hPn⟩ := factorial_actual_potential_commutator_L2 F W r N hN0 hW hN
    B M A hM hA hBmeas hBbound (mixedMultiIndexWord α β)
    (by simpa only [factorialWordYCount_mixedMultiIndexWord,
      factorialWordTCount_mixedMultiIndexWord] using hc)
  obtain ⟨HQ,hQ,hQn⟩ := factorial_principal_indexed_error_L2 c F W r (N (r-1)) (N (r-2))
    hW (hN (r-1) le_rfl) (hN (r-2) (by omega)) α β hc
  refine ⟨HS-HP+HQ,?_,?_⟩
  · filter_upwards [Lp.coeFn_add (HS-HP) HQ,Lp.coeFn_sub HS HP,hS,hP,hQ] with p hadd hsub hs hp hq
    rw [hadd]
    change (HS-HP) p+HQ p = _
    rw [hsub]
    change HS p-HP p+HQ p = _
    rw [hs,hp,hq,mixedMultiIndexGrushinSource_closed]
  · calc
      ‖HS-HP+HQ‖ ≤ ‖HS-HP‖+‖HQ‖ := norm_add_le _ _
      _ ≤ (‖HS‖+‖HP‖)+‖HQ‖ := add_le_add (norm_sub_le HS HP) le_rfl
      _ ≤ _ := add_le_add (add_le_add hSn hPn) hQn

#print axioms factorial_differentiated_source_L2
end TheoremT.Continuum.WeakGrushin
