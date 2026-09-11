import HydrogenHarmonicPolynomial_v1

/-! Finite algebraic harmonic decomposition in three real variables. The span
means finite linear combinations of the displayed actual polynomials. Its
geometric interpretation on the sphere is a separate obligation. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace TheoremT.HydrogenPolynomial

abbrev Polynomial3 := MvPolynomial (Fin 3) ℝ

def harmonicGenerators (k : ℕ) : Set Polynomial3 :=
  {P | ∃ (j m : ℕ) (H : Polynomial3),
    2 * j + m = k ∧ H.IsHomogeneous m ∧ polynomialLaplace H = 0 ∧
      P = radiusSquared ^ j * H}

def harmonicSpan (k : ℕ) : Submodule ℝ Polynomial3 :=
  Submodule.span ℝ (harmonicGenerators k)

theorem polynomialLaplace_add (P Q : Polynomial3) :
    polynomialLaplace (P + Q) = polynomialLaplace P + polynomialLaplace Q := by
  simp [polynomialLaplace, map_add, Finset.sum_add_distrib]

theorem polynomialLaplace_smul (c : ℝ) (P : Polynomial3) :
    polynomialLaplace (c • P) = c • polynomialLaplace P := by
  simp [polynomialLaplace, Finset.smul_sum]

theorem polynomialLaplace_zero : polynomialLaplace (0 : Polynomial3) = 0 := by
  simp [polynomialLaplace]

theorem harmonicSpan_isHomogeneous {k : ℕ} {P : Polynomial3}
    (hP : P ∈ harmonicSpan k) : P.IsHomogeneous k := by
  apply (show harmonicSpan k ≤ homogeneousSubmodule (Fin 3) ℝ k from ?_) hP
  apply Submodule.span_le.mpr
  rintro P ⟨j, m, H, heq, hH, _, rfl⟩
  rw [← heq]
  exact (radiusSquared_isHomogeneous.pow j).mul hH

theorem harmonic_mem_span {k : ℕ} {H : Polynomial3}
    (hH : H.IsHomogeneous k) (hL : polynomialLaplace H = 0) :
    H ∈ harmonicSpan k := by
  exact Submodule.subset_span ⟨0, k, H, by omega, hH, hL, by simp⟩

theorem polynomialLaplace_isHomogeneous {k : ℕ} {P : Polynomial3}
    (hP : P.IsHomogeneous k) : (polynomialLaplace P).IsHomogeneous (k - 2) := by
  apply IsHomogeneous.sum
  intro i _
  simpa [Nat.sub_sub] using (hP.pderiv (i := i)).pderiv (i := i)

theorem polynomialLaplace_eq_zero_of_degree_le_one {k : ℕ} {P : Polynomial3}
    (hP : P.IsHomogeneous k) (hk : k ≤ 1) : polynomialLaplace P = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : (pderiv i P).IsHomogeneous 0 := by
    simpa [show k - 1 = 0 by omega] using hP.pderiv (i := i)
  have he := (totalDegree_zero_iff_isHomogeneous (Fin 3)).mpr hi
  rw [totalDegree_eq_zero_iff_eq_C] at he
  rw [he, pderiv_C]

theorem harmonicSpan_laplace_lift {k : ℕ} (hk : 2 ≤ k)
    {P : Polynomial3} (hP : P ∈ harmonicSpan (k - 2)) :
    ∃ Q ∈ harmonicSpan k, polynomialLaplace Q = P := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨j, m, H, hdegree, hH, hL, rfl⟩ := hP
    let a : ℕ := 2 * (j + 1) * (2 * m + 2 * (j + 1) + 1)
    have ha : (a : ℝ) ≠ 0 := by dsimp [a]; positivity
    have hg : radiusSquared ^ (j + 1) * H ∈ harmonicSpan k :=
      Submodule.subset_span ⟨j + 1, m, H, by omega, hH, hL, rfl⟩
    refine ⟨(a : ℝ)⁻¹ • (radiusSquared ^ (j + 1) * H),
      (harmonicSpan k).smul_mem _ hg, ?_⟩
    rw [polynomialLaplace_smul, polynomialLaplace_radius_pow_mul_harmonic_succ hH hL]
    change (a : ℝ)⁻¹ • ((a : Polynomial3) * (radiusSquared ^ j * H)) = _
    rw [← show (a : ℝ) • (radiusSquared ^ j * H) =
      (a : Polynomial3) * (radiusSquared ^ j * H) by
        rw [smul_eq_C_mul]; simp]
    rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
  | zero => exact ⟨0, (harmonicSpan k).zero_mem, polynomialLaplace_zero⟩
  | add P Q _ _ hP hQ =>
    obtain ⟨A, hA, rfl⟩ := hP
    obtain ⟨B, hB, rfl⟩ := hQ
    exact ⟨A + B, (harmonicSpan k).add_mem hA hB, polynomialLaplace_add A B⟩
  | smul c P _ hP =>
    obtain ⟨A, hA, rfl⟩ := hP
    exact ⟨c • A, (harmonicSpan k).smul_mem c hA, polynomialLaplace_smul c A⟩

theorem homogeneous_mem_harmonicSpan {k : ℕ} {P : Polynomial3}
    (hP : P.IsHomogeneous k) : P ∈ harmonicSpan k := by
  induction k using Nat.strong_induction_on generalizing P with
  | h k ih =>
    by_cases hk : k ≤ 1
    · exact harmonic_mem_span hP (polynomialLaplace_eq_zero_of_degree_le_one hP hk)
    · have hk2 : 2 ≤ k := by omega
      have hD := ih (k - 2) (by omega) (polynomialLaplace_isHomogeneous hP)
      obtain ⟨Q, hQ, hL⟩ := harmonicSpan_laplace_lift hk2 hD
      have hPQ : polynomialLaplace (P - Q) = 0 := by
        simp only [polynomialLaplace, map_sub, Finset.sum_sub_distrib]
        change polynomialLaplace P - polynomialLaplace Q = 0
        rw [hL, sub_self]
      have hh := harmonic_mem_span (hP.sub (harmonicSpan_isHomogeneous hQ)) hPQ
      simpa using (harmonicSpan k).add_mem hh hQ

theorem harmonicSpan_eq_homogeneousSubmodule (k : ℕ) :
    harmonicSpan k = homogeneousSubmodule (Fin 3) ℝ k := by
  ext P
  exact ⟨harmonicSpan_isHomogeneous, homogeneous_mem_harmonicSpan⟩

end TheoremT.HydrogenPolynomial
