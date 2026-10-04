import ActualL2IntegralCauchy_v1
import SpectatorIterationState_v1
import GrushinFactorialIndexRowBudget_v1
import SmoothComplexMixedSourceWords_v1
import MixedMultiIndexWord_v1

/-! Convert actual squared source budgets to the L2 representative needed
by the differentiated-source bound. The original source budget is an explicit
analytic-data hypothesis; the representative and cost-order bound are proved.
No executable representation or new solution regularity is claimed. -/
noncomputable section
open MeasureTheory Filter
open scoped BigOperators
namespace TheoremT.Continuum.WeakGrushin

theorem RegionL2Budget.exists_L2_norm_le
    {Ω : Set (Space (Fin 3))} {f : Space (Fin 3) → ℂ} {U : ℝ}
    (hU : 0 ≤ U) (hf : RegionL2Budget f Ω (U^2)) :
    ∃ H : Lp ℂ 2 (volume.restrict Ω), H =ᵐ[volume.restrict Ω] f ∧ ‖H‖ ≤ U := by
  refine ⟨hf.1.toLp f,hf.1.coeFn_toLp,?_⟩
  have hs : ‖hf.1.toLp f‖^2 ≤ U^2 := by
    rw [actual_l2_toLp_norm_sq_integral]
    exact hf.2
  nlinarith [norm_nonneg (hf.1.toLp f)]

theorem factorial_growth_mono {A : ℝ} (hA : 1 ≤ A) {k r : ℕ} (hkr : k ≤ r) :
    A^k*(k.factorial : ℝ) ≤ A^r*(r.factorial : ℝ) := by
  have hp : A^k ≤ A^r := pow_le_pow_right₀ hA hkr
  have hf : (k.factorial : ℝ) ≤ (r.factorial : ℝ) := by
    exact_mod_cast Nat.factorial_le hkr
  exact mul_le_mul hp hf (Nat.cast_nonneg _) (pow_nonneg (zero_le_one.trans hA) _)

theorem factorial_source_budget_representative
    {Ω O : Set (Space (Fin 3))} (hO : O ⊆ Ω)
    (s : Space (Fin 3) → ℂ) {F A : ℝ} (hF : 0 ≤ F) (hA : 1 ≤ A)
    (hbudget : ∀ w : List (Fin 4 ⊕ Fin 3),
      RegionL2Budget (complexDirectionalWordDeriv productCoordinateDirection s w) Ω
        ((F*A^w.length*(w.length.factorial : ℝ))^2))
    {r : ℕ} (α : Fin 4 → ℕ) (β : Fin 3 → ℕ)
    (hcost : factorialMultiDerivativeCost α β ≤ r) :
    ∃ H : Lp ℂ 2 (volume.restrict O),
      H =ᵐ[volume.restrict O]
        complexDirectionalWordDeriv productCoordinateDirection s (mixedMultiIndexWord α β) ∧
      ‖H‖ ≤ F*A^r*(r.factorial : ℝ) := by
  have hlen : (mixedMultiIndexWord α β).length ≤ r := by
    rw [mixedMultiIndexWord_length]
    exact (factorialDerivativeCost_total_le (∑ i,α i) (∑ j,β j)).trans hcost
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  obtain ⟨H,hH,hn⟩ := ((hbudget (mixedMultiIndexWord α β)).restrict hO le_rfl).exists_L2_norm_le
    (by positivity)
  refine ⟨H,hH,hn.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (factorial_growth_mono hA hlen) hF

end TheoremT.Continuum.WeakGrushin
