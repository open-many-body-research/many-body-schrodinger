import HydrogenPolynomialDensityCoordinate_v1

/-! Exact commutation and global derivative identities for finite coordinate
Bernstein operators. These hold before imposing any approximation norm. -/
noncomputable section
open scoped BigOperators
namespace TheoremT.HydrogenPolynomialDensity
variable {ι : Type*} [DecidableEq ι]

theorem coordinateBernstein_commute {i j : ι} (hij : i ≠ j)
    (m n : ℕ) (f : (ι → ℝ) → ℝ) :
    coordinateBernstein m i (coordinateBernstein n j f) =
      coordinateBernstein n j (coordinateBernstein m i f) := by
  funext x
  simp_rw [coordinateBernstein_eq_sum, Function.update_of_ne hij,
    Function.update_of_ne hij.symm, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro k _
  rw [Function.update_comm hij]
  ring

theorem coordinateBernstein_continuous
    (n : ℕ) (i : ι) {f : (ι → ℝ) → ℝ} (hf : Continuous f) :
    Continuous (coordinateBernstein n i f) := by
  change Continuous (fun x => coordinateBernstein n i f x)
  simp_rw [coordinateBernstein_eq_sum]
  apply continuous_finset_sum
  intro k _
  apply Continuous.mul
  · exact (bernsteinPolynomial ℝ n k).continuous.comp (continuous_apply i)
  · exact hf.comp (by fun_prop)

theorem coordinateBernstein_other_hasDerivAt {i j : ι} (hij : i ≠ j)
    (n : ℕ) {f g : (ι → ℝ) → ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f (Function.update y j t)) (g y) (y j))
    (x : ι → ℝ) :
    HasDerivAt (fun t => coordinateBernstein n i f (Function.update x j t))
      (coordinateBernstein n i g x) (x j) := by
  have hdiff (k : ℕ) (_ : k ∈ Finset.range (n + 1)) :
      HasDerivAt
        (fun t => (bernsteinPolynomial ℝ n k).eval (x i) *
          f (Function.update (Function.update x i ((k : ℝ) / n)) j t))
        ((bernsteinPolynomial ℝ n k).eval (x i) *
          g (Function.update x i ((k : ℝ) / n))) (x j) := by
    have hd := (hf (Function.update x i ((k : ℝ) / n))).const_mul
      ((bernsteinPolynomial ℝ n k).eval (x i))
    simpa [Function.update_of_ne hij.symm] using hd
  have hs := HasDerivAt.fun_sum hdiff
  simp_rw [coordinateBernstein_eq_sum, Function.update_of_ne hij]
  simpa only [Function.update_comm hij] using hs

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.coordinateBernstein_commute
#print axioms TheoremT.HydrogenPolynomialDensity.coordinateBernstein_other_hasDerivAt
