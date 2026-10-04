import HomogeneousSpectatorSeriesMajorant_v1
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-! Absolute and uniform convergence of the actual double-index polynomial
and spectator series on a product of two literal closed complex polydiscs. -/
noncomputable section
set_option autoImplicit false
open scoped BigOperators
namespace TheoremT.Continuum

theorem homogeneous_spectator_series_closed_polydiscs {d : ℕ}
    (A : ℕ → (Fin d → ℕ) → MvPolynomial (Fin 3) ℂ)
    (hA : ∀ m γ, (A m γ).IsHomogeneous m)
    {M D r S h : ℝ} (hM : 0 ≤ M) (hD : 0 ≤ D) (hr : 0 ≤ r)
    (hS : 0 ≤ S) (hh : 0 ≤ h) (hDr : D*r < 1) (hSh : S*h < 1)
    (hL : ∀ m γ, polynomialCoeffL1 (A m γ) ≤ M*D^m*S^(∑ i : Fin d, γ i)) :
    (∀ z ∈ complexClosedPolydisc (Fin 3) r ×ˢ complexClosedPolydisc (Fin d) h,
      Summable (fun k : ℕ × (Fin d → ℕ) => ‖homogeneousSpectatorTerm A k z‖) ∧
      Summable (fun k : ℕ × (Fin d → ℕ) => homogeneousSpectatorTerm A k z) ∧
      ‖∑' k : ℕ × (Fin d → ℕ), homogeneousSpectatorTerm A k z‖ ≤
        M/((1-D*r)*(1-S*h)^d)) ∧
    HasSumUniformlyOn (homogeneousSpectatorTerm A)
      (fun z => ∑' k : ℕ × (Fin d → ℕ), homogeneousSpectatorTerm A k z)
      (complexClosedPolydisc (Fin 3) r ×ˢ complexClosedPolydisc (Fin d) h) := by
  have hu := homogeneous_spectator_majorant_hasSum d hM hD hr hS hh hDr hSh
  have hb := homogeneous_spectator_term_norm_bound A hA hr hh hL
  refine ⟨?_, HasSumUniformlyOn.of_norm_le_summable hu.summable hb⟩
  intro z hz
  have habs : Summable (fun k : ℕ × (Fin d → ℕ) => ‖homogeneousSpectatorTerm A k z‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => hb k z hz) hu.summable
  refine ⟨habs, habs.of_norm, ?_⟩
  calc
    _ ≤ ∑' k : ℕ × (Fin d → ℕ), ‖homogeneousSpectatorTerm A k z‖ := norm_tsum_le_tsum_norm habs
    _ ≤ ∑' k : ℕ × (Fin d → ℕ), homogeneousSpectatorMajorant M D r S h k :=
      habs.tsum_le_tsum (fun k => hb k z hz) hu.summable
    _ = M/((1-D*r)*(1-S*h)^d) := hu.tsum_eq

end TheoremT.Continuum
