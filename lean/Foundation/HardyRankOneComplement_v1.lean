import HardyTemple_v1

/-! A single rank-one form comparison forces the ground-orthogonal complement
separator for an eigenvalue below its threshold. All expansions are on the
actual operator domain; no moment, spectral, or finite-dimensional premise
is inserted. The comparison and eigenpair remain explicit hypotheses. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped InnerProductSpace LinearPMap
namespace TheoremT.OperatorTheory
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

theorem re_inner_smul_same (c : ℂ) (x y : H) :
    (inner ℂ (c • x) (c • y)).re = ‖c‖^2 * (inner ℂ x y).re := by
  rw [inner_smul_left, inner_smul_right, ← mul_assoc]
  simp [RCLike.conj_mul, pow_two, Complex.mul_re]

theorem rankOne_ground_functional_ne_zero (A : H →ₗ.[ℂ] H) (l : H →L[ℂ] ℂ)
    (C β : ℝ)
    (hbound : ∀ x : A.domain, β * ‖(x : H)‖^2 ≤
      (inner ℂ (x : H) (A x)).re + C * ‖l (x : H)‖^2)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β) : l (g : H) ≠ 0 := by
  intro hz
  have h := hbound g
  rw [hg, hEg, inner_smul_right, inner_self_eq_norm_sq_to_K, hg, hz] at h
  simp at h
  linarith

/-- The exact stronger inequality behind the complement estimate. It also
shows why the below-threshold eigenvector must be visible to the functional. -/
theorem rankOne_ground_complement_weighted (A : H →ₗ.[ℂ] H)
    (hsym : A.IsFormalAdjoint A) (l : H →L[ℂ] ℂ) (C β : ℝ)
    (hbound : ∀ x : A.domain, β * ‖(x : H)‖^2 ≤
      (inner ℂ (x : H) (A x)).re + C * ‖l (x : H)‖^2)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E : ℝ)
    (hEg : A g = (E : ℂ) • (g : H))
    (w : A.domain) (hgw : inner ℂ (g : H) (w : H) = 0) :
    (β - E) * ‖l (w : H)‖^2 ≤
      ‖l (g : H)‖^2 * ((inner ℂ (w : H) (A w)).re - β * ‖(w : H)‖^2) := by
  let v : A.domain := l (w : H) • g - l (g : H) • w
  have hvval : (v : H) = l (w : H) • (g : H) - l (g : H) • (w : H) := rfl
  have hlv : l (v : H) = 0 := by
    rw [hvval, map_sub, map_smul, map_smul]
    change l (w : H) * l (g : H) - l (g : H) * l (w : H) = 0
    ring
  have hAv : A v = l (w : H) • A g - l (g : H) • A w := by
    simp only [v, A.map_sub, A.map_smul]
  have hgwA : inner ℂ (g : H) (A w) = 0 := by
    rw [← hsym g w, hEg, inner_smul_left, hgw, mul_zero]
  have hwgA : inner ℂ (w : H) (A g) = 0 := by
    rw [hEg, inner_smul_right, inner_eq_zero_symm.mp hgw, mul_zero]
  have hqg : (inner ℂ (g : H) (A g)).re = E := by
    rw [hEg, inner_smul_right, inner_self_eq_norm_sq_to_K, hg]
    simp
  have hnorm : ‖(v : H)‖^2 = ‖l (w : H)‖^2 + ‖l (g : H)‖^2 * ‖(w : H)‖^2 := by
    rw [hvval, norm_sub_sq (𝕜 := ℂ)]
    simp [inner_smul_left, inner_smul_right, hgw, _root_.norm_smul, mul_pow, hg]
  have hinner : inner ℂ (v : H) (A v) =
      inner ℂ (l (w : H) • (g : H)) (l (w : H) • A g) +
        inner ℂ (l (g : H) • (w : H)) (l (g : H) • A w) := by
    rw [hvval, hAv]
    simp [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right, hgwA, hwgA]
  have hqv : (inner ℂ (v : H) (A v)).re =
      ‖l (w : H)‖^2 * E + ‖l (g : H)‖^2 * (inner ℂ (w : H) (A w)).re := by
    rw [hinner, Complex.add_re, re_inner_smul_same, re_inner_smul_same, hqg]
  have hb := hbound v
  rw [hnorm, hqv, hlv] at hb
  simp only [norm_zero, zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero] at hb
  nlinarith

theorem rankOne_ground_complement (A : H →ₗ.[ℂ] H) (hsym : A.IsFormalAdjoint A)
    (l : H →L[ℂ] ℂ) (C β : ℝ)
    (hbound : ∀ x : A.domain, β * ‖(x : H)‖^2 ≤
      (inner ℂ (x : H) (A x)).re + C * ‖l (x : H)‖^2)
    (g : A.domain) (hg : ‖(g : H)‖ = 1) (E : ℝ)
    (hEg : A g = (E : ℂ) • (g : H)) (hgap : E < β)
    (w : A.domain) (hgw : inner ℂ (g : H) (w : H) = 0) :
    β * ‖(w : H)‖^2 ≤ (inner ℂ (w : H) (A w)).re := by
  have hlg := rankOne_ground_functional_ne_zero A l C β hbound g hg E hEg hgap
  have hs := rankOne_ground_complement_weighted A hsym l C β hbound g hg E hEg w hgw
  have hpos : 0 < ‖l (g : H)‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hlg)
  have hn : 0 ≤ (β - E) * ‖l (w : H)‖^2 :=
    mul_nonneg (sub_pos.mpr hgap).le (sq_nonneg _)
  nlinarith

#print axioms rankOne_ground_functional_ne_zero
#print axioms rankOne_ground_complement_weighted
#print axioms rankOne_ground_complement
end TheoremT.OperatorTheory
