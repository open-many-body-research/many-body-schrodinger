import HydrogenHarmonicDecomposition_v1

/-! Every polynomial restricted to the radius-one algebraic sphere is a
finite linear combination of homogeneous harmonic polynomial restrictions.
This gives the algebraic part of the angular argument, without assuming a
spherical Laplacian or any analytic density theorem. -/
noncomputable section
open MvPolynomial
open scoped BigOperators
namespace TheoremT.HydrogenPolynomial

def UnitSphere3 := {x : Fin 3 → ℝ // ∑ i, x i ^ 2 = 1}

def spherePolynomialEvaluation : Polynomial3 →ₗ[ℝ] (UnitSphere3 → ℝ) where
  toFun P x := eval x.val P
  map_add' P Q := by ext x; exact map_add _ P Q
  map_smul' c P := by ext x; simp

def harmonicSphereSpan : Submodule ℝ (UnitSphere3 → ℝ) :=
  Submodule.span ℝ {f | ∃ (m : ℕ) (H : Polynomial3),
    H.IsHomogeneous m ∧ polynomialLaplace H = 0 ∧ f = spherePolynomialEvaluation H}

theorem eval_radiusSquared_unitSphere (x : UnitSphere3) :
    eval x.val (radiusSquared : Polynomial3) = 1 := by
  simpa [radiusSquared] using x.property

theorem spherePolynomialEvaluation_radius_pow_mul (j : ℕ) (H : Polynomial3) :
    spherePolynomialEvaluation (radiusSquared ^ j * H) = spherePolynomialEvaluation H := by
  ext x
  change eval x.val (radiusSquared ^ j * H) = eval x.val H
  rw [map_mul, map_pow, eval_radiusSquared_unitSphere]
  simp

theorem sphere_harmonicSpan_inclusion {k : ℕ} {P : Polynomial3}
    (hP : P ∈ harmonicSpan k) : spherePolynomialEvaluation P ∈ harmonicSphereSpan := by
  induction hP using Submodule.span_induction with
  | mem P hP =>
    obtain ⟨j, m, H, _, hH, hL, rfl⟩ := hP
    rw [spherePolynomialEvaluation_radius_pow_mul]
    exact Submodule.subset_span ⟨m, H, hH, hL, rfl⟩
  | zero => simpa using harmonicSphereSpan.zero_mem
  | add P Q _ _ hP hQ =>
    simpa using harmonicSphereSpan.add_mem hP hQ
  | smul c P _ hP =>
    simpa using harmonicSphereSpan.smul_mem c hP

theorem spherePolynomialEvaluation_mem_harmonicSphereSpan (P : Polynomial3) :
    spherePolynomialEvaluation P ∈ harmonicSphereSpan := by
  have hsum : spherePolynomialEvaluation
      (∑ i ∈ Finset.range (P.totalDegree + 1), homogeneousComponent i P) ∈
        harmonicSphereSpan := by
    rw [map_sum]
    apply harmonicSphereSpan.sum_mem
    intro i _
    exact sphere_harmonicSpan_inclusion
      (homogeneous_mem_harmonicSpan (homogeneousComponent_isHomogeneous i P))
  simpa only [sum_homogeneousComponent] using hsum

end TheoremT.HydrogenPolynomial
