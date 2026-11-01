import CompactWeakFactorialOuterBound_v1
import FactorialOuterL2Uniqueness_v1

/-! Complete compact weak Grushin outer estimate with literal derivative
semantics. The witnesses are actual L2 coordinate derivatives through order
two, retain the original support, and have exact compact-test identities.
All 498 weighted L2 components are constructed and their sum of norms is
bounded by the actual principal output. This is not an all-order theorem. -/
noncomputable section
open MeasureTheory Filter
open scoped ContDiff BigOperators
set_option maxRecDepth 4096
namespace TheoremT.Continuum.WeakGrushin

theorem compact_weak_grushin_outer_maximal_with_tests
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
    ∃ D : (Fin 4 → ℕ) → (Fin 3 → ℕ) → Lp ℂ 2 (volume : Measure (Space (Fin 3))),
      D 0 0 = f ∧
      (∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 →
        ∀ᵐ p ∂volume, p ∉ K → D α β p = 0) ∧
      (∀ α β, (∑ i, α i)+(∑ j, β j) ≤ 2 →
        ∀ φ : Space (Fin 3) → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ →
          Integrable (fun p => φ p • D α β p) ∧
          Integrable (fun p => productCoordinateTestWord (mixedMultiIndexWord α β) φ p • f p) ∧
          (∫ p, φ p • D α β p) = ((-1 : ℝ)^((∑ i, α i)+(∑ j, β j))) •
            (∫ p, productCoordinateTestWord (mixedMultiIndexWord α β) φ p • f p)) ∧
      ∃ W : FactorialOuterIndex → Lp ℂ 2 (volume : Measure (Space (Fin 3))),
        FactorialOuterL2Rep (fun α β => (D α β : Space (Fin 3) → ℂ)) W ∧
        factorialOuterNorm W ≤ 498*S^2*(4*R^2+2*R+2+2/c)*‖h‖ := by
  refine ⟨weakFactorialJet f d e,weakFactorialJet_zero f d e,?_,?_,?_⟩
  · intro α β _
    exact weakFactorialJet_closed_support f d e hd he hK.isClosed hs α β
  · intro α β horder φ hφ hcφ
    exact weakFactorialJet_tests f d e hd he α β horder hφ hcφ
  · exact compact_weak_factorial_outer_graph_bound hc d e hd he hK hs hP i₀ hR hslab S hS hSK

end TheoremT.Continuum.WeakGrushin
