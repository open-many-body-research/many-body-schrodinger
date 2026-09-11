import HydrogenPolynomialDensityStability_v1

/-! Coordinate Bernstein operators on actual finite-dimensional real functions.
They contract uniform errors on the cube, have the actual forward-difference
derivative in their own coordinate, and commute with differentiation in a
different coordinate. These are finite-sum identities, not density premises. -/
noncomputable section
open scoped Polynomial BigOperators unitInterval
open Set
namespace TheoremT.HydrogenPolynomialDensity

variable {ι : Type*} [DecidableEq ι]

def inUnitCube (x : ι → ℝ) : Prop := ∀ i, x i ∈ Icc (0 : ℝ) 1

def coordinateBernstein (n : ℕ) (i : ι) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ :=
  (gridBernsteinPolynomial n (fun t => f (Function.update x i t))).eval (x i)

theorem coordinateBernstein_eq_sum (n : ℕ) (i : ι) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    coordinateBernstein n i f x =
      ∑ k ∈ Finset.range (n + 1),
        (bernsteinPolynomial ℝ n k).eval (x i) *
          f (Function.update x i ((k : ℝ) / n)) := by
  simp only [coordinateBernstein, gridBernsteinPolynomial, bernsteinCombination,
    Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C]
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem inUnitCube_update {x : ι → ℝ} (hx : inUnitCube x) (i : ι) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) 1) : inUnitCube (Function.update x i t) := by
  intro j
  by_cases hji : j = i
  · subst j
    simpa using ht
  · simpa [Function.update_of_ne hji] using hx j

theorem coordinateBernstein_sup_stability (n : ℕ) (i : ι)
    (f g : (ι → ℝ) → ℝ) {δ : ℝ}
    (h : ∀ y, inUnitCube y → |f y - g y| ≤ δ)
    (x : ι → ℝ) (hx : inUnitCube x) :
    |coordinateBernstein n i f x - coordinateBernstein n i g x| ≤ δ := by
  apply bernsteinCombination_sup_stability n
    (fun k => f (Function.update x i ((k : ℝ) / n)))
    (fun k => g (Function.update x i ((k : ℝ) / n)))
    (fun k hk => h _ (inUnitCube_update hx i ?_)) (⟨x i, hx i⟩ : I)
  exact (bernstein.z (⟨k, Nat.lt_succ_of_le hk⟩ : Fin (n + 1))).property

/-- In the sampled coordinate the output is literally a polynomial in the
replacement coordinate, for an arbitrary input function. -/
theorem coordinateBernstein_own_slice (n : ℕ) (i : ι) (f : (ι → ℝ) → ℝ)
    (x : ι → ℝ) (t : ℝ) :
    coordinateBernstein n i f (Function.update x i t) =
      (gridBernsteinPolynomial n (fun u => f (Function.update x i u))).eval t := by
  simp [coordinateBernstein]

theorem coordinateBernstein_own_hasDerivAt (n : ℕ) (i : ι)
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun u => coordinateBernstein (n + 1) i f (Function.update x i u))
      ((bernsteinCombination n
        (fun k => forwardGridDifference n k (fun u => f (Function.update x i u)))).eval t) t := by
  simp_rw [coordinateBernstein_own_slice]
  exact gridBernsteinPolynomial_hasDerivAt n _ t

/-- Sampling another coordinate commutes with the actual slice derivative. -/
theorem coordinateBernstein_other_hasDerivWithinAt {i j : ι} (hij : i ≠ j)
    (n : ℕ) {f g : (ι → ℝ) → ℝ} {x : ι → ℝ} (hx : inUnitCube x)
    (hf : ∀ y, inUnitCube y →
      HasDerivWithinAt (fun t => f (Function.update y j t)) (g y) (Icc 0 1) (y j)) :
    HasDerivWithinAt (fun t => coordinateBernstein n i f (Function.update x j t))
      (coordinateBernstein n i g x) (Icc 0 1) (x j) := by
  have hdiff (k : ℕ) (hk : k ∈ Finset.range (n + 1)) :
      HasDerivWithinAt
        (fun t => (bernsteinPolynomial ℝ n k).eval (x i) *
          f (Function.update (Function.update x i ((k : ℝ) / n)) j t))
        ((bernsteinPolynomial ℝ n k).eval (x i) *
          g (Function.update x i ((k : ℝ) / n))) (Icc 0 1) (x j) := by
    have hgrid : (k : ℝ) / n ∈ Icc (0 : ℝ) 1 :=
      (bernstein.z (⟨k, Finset.mem_range.mp hk⟩ : Fin (n + 1))).property
    have hd := (hf _ (inUnitCube_update hx i hgrid)).const_mul
      ((bernsteinPolynomial ℝ n k).eval (x i))
    simpa [Function.update_of_ne hij.symm] using hd
  have hs := HasDerivWithinAt.fun_sum hdiff
  simp_rw [coordinateBernstein_eq_sum, Function.update_of_ne hij]
  simpa only [Function.update_comm hij] using hs

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.coordinateBernstein_sup_stability
#print axioms TheoremT.HydrogenPolynomialDensity.coordinateBernstein_own_hasDerivAt
#print axioms TheoremT.HydrogenPolynomialDensity.coordinateBernstein_other_hasDerivWithinAt
