import HydrogenPolynomialDensityCoordinate_v1
import HydrogenPolynomialDensityFamilyC0_v1

/-! Uniform convergence of the actual coordinate Bernstein operator on the
unit cube.  The compact parameter space is the product of unit intervals. -/

noncomputable section
open scoped unitInterval BigOperators
open Set
namespace TheoremT.HydrogenPolynomialDensityCoordinateC0
open TheoremT.HydrogenPolynomialDensity
open TheoremT.HydrogenPolynomialDensityFamilyC0

variable {ι : Type*} [DecidableEq ι]

/-- A single coordinate Bernstein operator approximates a continuous function
uniformly over the entire unit cube. Compactness of a product of unit intervals
allows even an arbitrary index type here; finite-dimensional tensorization is
an immediate specialization. -/
theorem coordinateBernstein_uniform {f : (ι → ℝ) → ℝ}
    (hf : Continuous f) (i : ι) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ x : ι → ℝ, inUnitCube x →
      |coordinateBernstein n i f x - f x| < ε := by
  let F : C((ι → I) × I, ℝ) :=
    ⟨fun p => f (Function.update (fun j => (p.1 j : ℝ)) i (p.2 : ℝ)),
      hf.comp (by fun_prop)⟩
  obtain ⟨n₀, hn₀⟩ := familyBernstein_uniform F hε
  refine ⟨n₀, ?_⟩
  intro n hn x hx
  let y : ι → I := fun j => ⟨x j, hx j⟩
  let t : I := ⟨x i, hx i⟩
  have heq : coordinateBernstein n i f x = familyBernstein F n y t := by
    change (bernsteinCombination n (fun k => f (Function.update x i ((k : ℝ) / n)))).eval
      (t : ℝ) = _
    rw [bernsteinCombination_eval]
    unfold familyBernstein
    apply Finset.sum_congr rfl
    intro k _
    change f (Function.update x i ((k : ℕ) / (n : ℝ))) * bernstein n k t =
      bernstein n k t * f (Function.update x i ((k : ℕ) / (n : ℝ)))
    exact mul_comm _ _
  have hval : F (y, t) = f x := by
    change f (Function.update x i (x i)) = f x
    rw [Function.update_eq_self]
  rw [heq, ← hval]
  exact hn₀ n hn y t

end TheoremT.HydrogenPolynomialDensityCoordinateC0

#print axioms TheoremT.HydrogenPolynomialDensityCoordinateC0.coordinateBernstein_uniform
