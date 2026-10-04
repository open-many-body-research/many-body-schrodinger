import WeakFactorialOuterCompatible_v1
import WeakFactorialJetIdentifications_v2
import WeakFactorialJetTests_v1

/-! The exact full outer weighted norm bound for genuine compact weak H2
inputs. Canonical low-order representatives and all 498 monomial-weighted
L2 outputs are constructed from actual weak jets and the actual weak
Grushin output. No smoothness of the input or outer-norm premise is used. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem compact_weak_factorial_outer_graph_bound
    {c : ℝ} (hc : 0 < c)
    {f h : Lp ℂ 2 (volume : Measure (Space (Fin 3)))}
    (d : Space (Fin 3) → Lp ℂ 2 (volume : Measure (Space (Fin 3)))) (e : Jet (Fin 3))
    (hd : ∀ v, WeakProductL2Directional f (d v) v)
    (he : ∀ v w, WeakProductL2Directional (d v) (e v w) w)
    {K : Set (Space (Fin 3))} (hK : IsCompact K)
    (hs : ∀ᵐ p ∂volume, p ∉ K → f p = 0)
    (hP : ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      (∫ p, splitGrushin c oscillatorBasis (fun _ => 0) φ p • f p) = ∫ p, φ p • h p)
    (i₀ : Fin 4) {R : ℝ} (hR : 0 < R) (hslab : ∀ p ∈ K, |p.1 i₀| ≤ R)
    (S : ℝ) (hS : 1 ≤ S) (hSK : ∀ p ∈ K, ‖p.1‖ ≤ S) :
    ∃ W : FactorialOuterIndex → Lp ℂ 2 (volume : Measure (Space (Fin 3))),
      FactorialOuterL2Rep
        (fun α β => (weakFactorialJet f d e α β : Space (Fin 3) → ℂ)) W ∧
      factorialOuterNorm W ≤ 498*S^2*(factorialGraphCoefficient R c)*‖h‖ := by
  apply compact_weak_compatible_factorial_outer_bound hc d e hd he hK hs hP i₀ hR hslab S hS hSK
  exact ⟨weakFactorialJet_zero f d e,
    weakFactorialJet_single_y f d e,weakFactorialJet_single_t f d e,
    weakFactorialJet_double_y d e hd he hK hs,
    weakFactorialJet_mixed d e hd he hK hs,
    weakFactorialJet_double_t d e hd he hK hs⟩

end TheoremT.Continuum.WeakGrushin
