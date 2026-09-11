import HydrogenPolynomialDensityTensorPolynomial_v1
import HydrogenPolynomialDensityCoordinateC1_v1

/-! C1 convergence of a single, actual three-variable Bernstein polynomial
family on the unit cube. The function and all three first derivatives are
approximated together. No multivariate density or sphere inequality is assumed. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.HydrogenPolynomialDensity
open TheoremT.HydrogenPolynomialDensityCoordinateC1

def otherCoordinates3 (i : Fin 3) : List (Fin 3) :=
  if i = 0 then [1, 2] else if i = 1 then [0, 2] else [0, 1]

theorem not_mem_otherCoordinates3 (i : Fin 3) : i ∉ otherCoordinates3 i := by
  fin_cases i <;> simp [otherCoordinates3]

theorem fold3_eq_other_own (n : ℕ) (i : Fin 3) (f : (Fin 3 → ℝ) → ℝ) :
    coordinateFold n [0, 1, 2] f =
      coordinateFold n (otherCoordinates3 i) (coordinateBernstein n i f) := by
  fin_cases i
  · simpa [otherCoordinates3, coordinateFold] using
      (coordinateFold_commute n n [1, 2] (0 : Fin 3) (by decide) f).symm
  · simp only [otherCoordinates3, Fin.zero_eta, Fin.isValue, Fin.mk_one,
      show (1 : Fin 3) ≠ 0 by decide, if_false, if_true,
      coordinateFold, List.foldr_cons, List.foldr_nil]
    exact congrArg (coordinateBernstein n (0 : Fin 3))
      (coordinateBernstein_commute (by decide : (1 : Fin 3) ≠ 2) n n f)
  · simp [otherCoordinates3, coordinateFold]

def tensorBernsteinDerivative3 (n : ℕ) (i : Fin 3) (f : (Fin 3 → ℝ) → ℝ) :
    (Fin 3 → ℝ) → ℝ :=
  coordinateFold (n + 1) (otherCoordinates3 i) (ownBernsteinDerivative n i f)

theorem tensorBernsteinPolynomial3_hasDerivAt (n : ℕ) (i : Fin 3)
    (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    HasDerivAt (fun t => MvPolynomial.eval (Function.update x i t)
      (tensorBernsteinPolynomial3 (n + 1) f))
      (tensorBernsteinDerivative3 n i f x) (x i) := by
  simp_rw [tensorBernsteinPolynomial3_eval]
  rw [fold3_eq_other_own (n + 1) i f]
  exact coordinateFold_other_hasDerivAt (n + 1) (otherCoordinates3 i) i
    (not_mem_otherCoordinates3 i) (ownBernsteinDerivative_hasDerivAt n i f) x

theorem tensorBernsteinPolynomial3_deriv (n : ℕ) (i : Fin 3)
    (f : (Fin 3 → ℝ) → ℝ) (x : Fin 3 → ℝ) :
    deriv (fun t => MvPolynomial.eval (Function.update x i t)
      (tensorBernsteinPolynomial3 (n + 1) f)) (x i) =
        tensorBernsteinDerivative3 n i f x :=
  (tensorBernsteinPolynomial3_hasDerivAt n i f x).deriv

theorem tensorBernsteinDerivative3_uniform {f g : (Fin 3 → ℝ) → ℝ}
    (hg : Continuous g) (i : Fin 3)
    (hf : ∀ y, HasDerivAt (fun t => f (Function.update y i t)) (g y) (y i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x, inUnitCube x →
      |tensorBernsteinDerivative3 n i f x - g x| < ε := by
  obtain ⟨nd, _, hnd⟩ := ownBernsteinDerivative_uniform hg i hf (half_pos hε)
  obtain ⟨nc, hnc⟩ := coordinateFold_uniform (otherCoordinates3 i) hg (half_pos hε)
  refine ⟨max nd nc, fun n hn x hx => ?_⟩
  have he := coordinateFold_sup_stability (n + 1) (otherCoordinates3 i)
    (ownBernsteinDerivative n i f) g
    (fun y hy => (hnd n ((le_max_left _ _).trans hn) y hy).le) x hx
  calc
    |tensorBernsteinDerivative3 n i f x - g x|
      ≤ |tensorBernsteinDerivative3 n i f x -
          coordinateFold (n + 1) (otherCoordinates3 i) g x| +
        |coordinateFold (n + 1) (otherCoordinates3 i) g x - g x| := abs_sub_le _ _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt he
      (hnc (n + 1) ((le_max_right _ _).trans (hn.trans (Nat.le_succ _))) x hx)
    _ = ε := add_halves ε

/-- Uniform value and all first-derivative convergence for the explicit tensor
Bernstein polynomials. The derivative in the conclusion is the actual analytic
derivative of polynomial evaluation along the coordinate line. -/
theorem tensorBernsteinPolynomial3_C1_uniform {f : (Fin 3 → ℝ) → ℝ}
    {g : Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hfc : Continuous f) (hgc : ∀ i, Continuous (g i))
    (hfg : ∀ i y, HasDerivAt (fun t => f (Function.update y i t)) (g i y) (y i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      (∀ x, inUnitCube x →
        |MvPolynomial.eval x (tensorBernsteinPolynomial3 (n + 1) f) - f x| < ε) ∧
      (∀ i x, inUnitCube x →
        |deriv (fun t => MvPolynomial.eval (Function.update x i t)
          (tensorBernsteinPolynomial3 (n + 1) f)) (x i) - g i x| < ε) := by
  obtain ⟨nf, hnf⟩ := coordinateFold_uniform [0, 1, 2] hfc hε
  have hds (i : Fin 3) := tensorBernsteinDerivative3_uniform (hgc i) i (hfg i) hε
  choose nd hnd using hds
  refine ⟨max nf (Finset.univ.sup nd), fun n hn => ⟨?_, ?_⟩⟩
  · intro x hx
    rw [tensorBernsteinPolynomial3_eval]
    exact hnf (n + 1) ((le_max_left _ _).trans (hn.trans (Nat.le_succ _))) x hx
  · intro i x hx
    rw [tensorBernsteinPolynomial3_deriv]
    apply hnd i n ?_ x hx
    exact (Finset.le_sup (f := nd) (Finset.mem_univ i)).trans ((le_max_right _ _).trans hn)

theorem exists_mvPolynomial3_C1_near {f : (Fin 3 → ℝ) → ℝ}
    {g : Fin 3 → (Fin 3 → ℝ) → ℝ}
    (hfc : Continuous f) (hgc : ∀ i, Continuous (g i))
    (hfg : ∀ i y, HasDerivAt (fun t => f (Function.update y i t)) (g i y) (y i))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : MvPolynomial (Fin 3) ℝ,
      (∀ x, inUnitCube x → |MvPolynomial.eval x p - f x| < ε) ∧
      (∀ i x, inUnitCube x →
        |deriv (fun t => MvPolynomial.eval (Function.update x i t) p) (x i) - g i x| < ε) := by
  obtain ⟨n, hn⟩ := tensorBernsteinPolynomial3_C1_uniform hfc hgc hfg hε
  exact ⟨tensorBernsteinPolynomial3 (n + 1) f, hn n le_rfl⟩

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.tensorBernsteinPolynomial3_hasDerivAt
#print axioms TheoremT.HydrogenPolynomialDensity.tensorBernsteinPolynomial3_C1_uniform
#print axioms TheoremT.HydrogenPolynomialDensity.exists_mvPolynomial3_C1_near
