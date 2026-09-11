import HardyTempleAlgebra_v1

/-! The rank-one decomposition required by Temple's inequality is performed
inside the actual linear operator domain. Every moment and residual identity
is derived from symmetry and the eigenvector; none is an input hypothesis. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped InnerProductSpace LinearPMap
namespace TheoremT.OperatorTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A conditional ground-branch estimate for an actual possibly unbounded
symmetric operator. The complement bound and eigenpair remain explicit. -/
theorem ground_complement_shift_estimate (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (g : A.domain) (hg : ‖(g : H)‖ = 1)
    (E β : ℝ) (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (hcomp : ∀ w : A.domain, inner ℂ (g : H) (w : H) = 0 →
      β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re)
    (ψ : A.domain) (hψ : ‖(ψ : H)‖ = 1) :
    0 ≤ (inner ℂ (ψ : H) (A ψ)).re - E ∧
      (β - E) * ((inner ℂ (ψ : H) (A ψ)).re - E) ≤
        ‖A ψ - (E : ℂ) • (ψ : H)‖^2 := by
  let α : ℂ := inner ℂ (g : H) (ψ : H)
  let w : A.domain := ψ - α • g
  let h : H := A ψ - (E : ℂ) • (ψ : H)
  let t : ℝ := (inner ℂ (ψ : H) (A ψ)).re - E
  have hwval : (w : H) = (ψ : H) - α • (g : H) := rfl
  have hgg : inner ℂ (g : H) (g : H) = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hg]
    norm_num
  have hgw : inner ℂ (g : H) (w : H) = 0 := by
    rw [hwval, inner_sub_right, inner_smul_right, hgg]
    change α - α * 1 = 0
    ring
  have hga : inner ℂ (g : H) (A ψ) =
      (E : ℂ) * inner ℂ (g : H) (ψ : H) := by
    rw [← hsym g ψ, hEg, inner_smul_left, Complex.conj_ofReal]
  have hgh : inner ℂ (g : H) h = 0 := by
    change inner ℂ (g : H) (A ψ - (E : ℂ) • (ψ : H)) = 0
    rw [inner_sub_right, inner_smul_right, hga, sub_self]
  have hAw : A w = A ψ - α • A g := by
    simp only [w, A.map_sub, A.map_smul]
  have hB : A w - (E : ℂ) • (w : H) = h := by
    rw [hAw, hEg, hwval]
    dsimp only [h]
    module
  have hph : (inner ℂ (ψ : H) h).re = t := by
    dsimp only [h, t]
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, hψ]
    simp
  have hwph : inner ℂ (w : H) h = inner ℂ (ψ : H) h := by
    rw [hwval, inner_sub_left, inner_smul_left, hgh, mul_zero, sub_zero]
  have hwt : (inner ℂ (w : H) h).re = t := by rw [hwph, hph]
  have htform : t = (inner ℂ (w : H) (A w)).re - E * ‖(w : H)‖^2 := by
    rw [← hwt, ← hB, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp [Complex.mul_re, ← Complex.ofReal_pow]
  have hβw := hcomp w hgw
  have htgap : (β - E) * ‖(w : H)‖^2 ≤ t := by rw [htform]; nlinarith
  have ht : 0 ≤ t := le_trans (mul_nonneg (sub_pos.mpr hgap).le (sq_nonneg _)) htgap
  have hcs0 : (inner ℂ (w : H) h).re ≤ ‖(w : H)‖ * ‖h‖ :=
    re_inner_le_norm (𝕜 := ℂ) (w : H) h
  rw [hwt] at hcs0
  have hcs : t^2 ≤ ‖(w : H)‖^2 * ‖h‖^2 := by
    simpa only [mul_pow] using pow_le_pow_left₀ ht hcs0 2
  exact ⟨ht, gap_cauchy_numeric (sub_pos.mpr hgap) (sq_nonneg ‖h‖) htgap ht hcs⟩

#print axioms ground_complement_shift_estimate
end TheoremT.OperatorTheory
