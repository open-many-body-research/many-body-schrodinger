import HydrogenPolynomialDensityCoordinateAlgebra_v1
import HydrogenPolynomialDensityCoordinateC0_v1

/-! Finite tensor products of coordinate Bernstein operators: contraction,
actual differentiation in unsampled coordinates, and uniform convergence. -/
noncomputable section
namespace TheoremT.HydrogenPolynomialDensity
variable {ι : Type*} [DecidableEq ι]

def coordinateFold (n : ℕ) (L : List ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  L.foldr (coordinateBernstein n) f

theorem coordinateFold_nil (n : ℕ) (f : (ι → ℝ) → ℝ) :
    coordinateFold n [] f = f := rfl

theorem coordinateFold_cons (n : ℕ) (i : ι) (L : List ι) (f : (ι → ℝ) → ℝ) :
    coordinateFold n (i :: L) f = coordinateBernstein n i (coordinateFold n L f) := rfl

theorem coordinateFold_sup_stability (n : ℕ) (L : List ι)
    (f g : (ι → ℝ) → ℝ) {δ : ℝ}
    (h : ∀ y, inUnitCube y → |f y - g y| ≤ δ)
    (x : ι → ℝ) (hx : inUnitCube x) :
    |coordinateFold n L f x - coordinateFold n L g x| ≤ δ := by
  induction L generalizing x with
  | nil => exact h x hx
  | cons i L ih =>
    exact coordinateBernstein_sup_stability n i _ _
      (fun y hy => ih y hy) x hx

theorem coordinateFold_continuous (n : ℕ) (L : List ι)
    {f : (ι → ℝ) → ℝ} (hf : Continuous f) : Continuous (coordinateFold n L f) := by
  induction L with
  | nil => exact hf
  | cons i L ih => exact coordinateBernstein_continuous n i ih

theorem coordinateFold_uniform (L : List ι) {f : (ι → ℝ) → ℝ}
    (hf : Continuous f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x, inUnitCube x →
      |coordinateFold n L f x - f x| < ε := by
  induction L generalizing ε with
  | nil => exact ⟨0, fun n hn x hx => by simpa [coordinateFold] using hε⟩
  | cons i L ih =>
    obtain ⟨n₀, hn₀⟩ := ih (half_pos hε)
    obtain ⟨n₁, hn₁⟩ :=
      HydrogenPolynomialDensityCoordinateC0.coordinateBernstein_uniform hf i (half_pos hε)
    refine ⟨max n₀ n₁, fun n hn x hx => ?_⟩
    have he := coordinateBernstein_sup_stability n i (coordinateFold n L f) f
      (fun y hy => (hn₀ n ((le_max_left _ _).trans hn) y hy).le) x hx
    calc
      |coordinateFold n (i :: L) f x - f x|
        ≤ |coordinateBernstein n i (coordinateFold n L f) x - coordinateBernstein n i f x| +
          |coordinateBernstein n i f x - f x| := abs_sub_le _ _ _
      _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt he
        (hn₁ n ((le_max_right _ _).trans hn) x hx)
      _ = ε := add_halves ε

theorem coordinateFold_commute (n m : ℕ) (L : List ι) (j : ι)
    (hj : j ∉ L) (f : (ι → ℝ) → ℝ) :
    coordinateFold n L (coordinateBernstein m j f) =
      coordinateBernstein m j (coordinateFold n L f) := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    have hji : j ≠ i := by simpa using fun h => hj (by simp [h])
    have hjL : j ∉ L := fun h => hj (by simp [h])
    rw [coordinateFold_cons, ih hjL, coordinateFold_cons]
    exact coordinateBernstein_commute hji.symm n m _

theorem coordinateFold_other_hasDerivAt (n : ℕ) (L : List ι) (j : ι)
    (hj : j ∉ L) {f g : (ι → ℝ) → ℝ}
    (hf : ∀ y, HasDerivAt (fun t => f (Function.update y j t)) (g y) (y j))
    (x : ι → ℝ) :
    HasDerivAt (fun t => coordinateFold n L f (Function.update x j t))
      (coordinateFold n L g x) (x j) := by
  induction L generalizing x with
  | nil => exact hf x
  | cons i L ih =>
    have hji : j ≠ i := by simpa using fun h => hj (by simp [h])
    have hjL : j ∉ L := fun h => hj (by simp [h])
    exact coordinateBernstein_other_hasDerivAt hji.symm n
      (fun y => ih hjL y) x

end TheoremT.HydrogenPolynomialDensity

#print axioms TheoremT.HydrogenPolynomialDensity.coordinateFold_uniform
#print axioms TheoremT.HydrogenPolynomialDensity.coordinateFold_other_hasDerivAt
