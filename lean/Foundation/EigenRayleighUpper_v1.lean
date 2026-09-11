import VariationalOperatorBridge_v2

/-! A nonzero actual continuum graph eigenvector bounds the normalized
variational infimum from above. This is a conditional implication: its
nonzero graph eigenvector is an explicit hypothesis, not constructed here. -/

noncomputable section
open MeasureTheory
open scoped InnerProductSpace

namespace TheoremT.Continuum

theorem variational_ground_le_graph_eigenvalue {N : ℕ} {Z E : ℝ} {ψ : SpinSpace N}
    (hψ : ψ ≠ 0) (hg : hamiltonianGraph N Z ψ ((E : ℂ) • ψ)) :
    variationalGroundEnergy N Z ≤ (E : EReal) := by
  let c : ℂ := (‖ψ‖ : ℂ)⁻¹
  have hn : ‖c • ψ‖ = 1 := by
    dsimp [c]
    rw [_root_.norm_smul, norm_inv, Complex.norm_real, norm_norm,
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hψ)]
  have hgn := hamiltonian_graph_smul c hg
  rw [smul_comm c (E : ℂ) ψ] at hgn
  have he : rayleighNumerator (c • ψ) ((E : ℂ) • (c • ψ)) = E := by
    rw [rayleighNumerator_eq_re_complex_inner, inner_smul_right,
      inner_self_eq_norm_sq_to_K, hn]
    simp
  have hup := variational_ground_le_trial hn hgn
  rw [he] at hup
  exact hup

end TheoremT.Continuum
